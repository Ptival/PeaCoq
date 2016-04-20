import { Feedback } from "./coq/feedback";
import { Message } from "./coq/message";
import { ValueFail } from "./coq/value-fail";
import * as CoqtopInput from "./coqtop-input";
import { Goals } from "./goals";
import { processSequentiallyForever } from "./rx";

let debugCoqtop = true; // print input/output requests
let statusPeriod = 250; // milliseconds

interface CoqtopResponse {
  input: CoqtopInput.CoqtopInput;
  tag: string;
  contents: Array<any>;
}

interface CoqtopOutput {
  response: CoqtopResponse;
  stateId: number;
  editId: number;
  messages: Object[];
  feedback: Object[];
}

interface CoqtopOutputStreams {
  error$: Rx.Observable<ValueFail>;
  feedback$: Rx.Observable<IFeedback>;
  goals$: Rx.Observable<Goals>;
  response$: Rx.Observable<CoqtopResponse>;
  message$: Rx.Observable<IMessage>;
  // stateId$: Rx.Observable<number>;
}

export function setupCoqtopCommunication(
  input$s: Rx.Observable<CoqtopInput.CoqtopInput>[]
): CoqtopOutputStreams {

  let inputStatus$: Rx.Observable<CoqtopInput.CoqtopInput> =
    Rx.Observable
      .interval(statusPeriod)
      .map(() => new CoqtopInput.Status(false));

  let inputSubject: Rx.Subject<CoqtopInput.CoqtopInput> =
    new Rx.Subject<CoqtopInput.CoqtopInput>();

  let input$: Rx.ConnectableObservable<CoqtopInput.CoqtopInput> =
    Rx.Observable
      .merge(
      inputStatus$,
      inputSubject.asObservable(),
      ...input$s
      )
      .publish();

  // subscribeAndLog(coqtopInputStream);

  let outputAndError$s = processSequentiallyForever<CoqtopInput.CoqtopInput, CoqtopOutput>(input$, processCommands);
  const output$ = outputAndError$s.output$;
  const error$ = outputAndError$s.error$
    .map(r => {
      return new ValueFail(r.response.contents);
    })
    .share();
  error$.subscribe(vf => inputSubject.onNext(new CoqtopInput.EditAt(vf.stateId)));

  let response$ = output$.map((r) => r.response);

  if (debugCoqtop) {
    input$
      .filter((i) => !(i instanceof CoqtopInput.Status))
      .subscribe((input) => { console.log("⟸", input); });
    response$
      .filter((r) => !(r.input instanceof CoqtopInput.Status))
      .subscribe((r) => { console.log("   ⟹", r.input, r); });
  }

  // this is needed for PeaCoq because we use add' so the STM's state
  // needs to be put back to where it worked
  // TODO: make a config flag for this feature
  error$.subscribe(e => {
    // console.log("sending EditAt because of error");
    inputSubject.onNext(new CoqtopInput.EditAt(e.stateId));
  });

  let addReponse$: Rx.Observable<AddReturn> =
    response$
      .filter((r) => r.input instanceof CoqtopInput.AddPrime)
      .map((r) => ({
        stateId: r.contents[0],
        eitherNullStateId: r.contents[1][0],
        output: r.contents[1][1],
      }))
    ;

  let stateId$ = output$.map((r) => r.stateId);

  let message$: Rx.Observable<IMessage> =
    output$
      .flatMap((r) => _(r.messages).map((m) => new Message(m)).value())
      .share();

  let feedback$: Rx.Observable<IFeedback> =
    output$
      .flatMap((r) => _(r.feedback).map((f) => new Feedback(f)).value())
      .share();

  let goals$: Rx.Observable<Goals> =
    response$
      .filter((r) => r.input instanceof CoqtopInput.Goal)
      .filter((r) => r.contents !== null)
      .map((r) => new Goals(r.contents));

  input$.connect();

  return {
    error$: error$,
    feedback$: feedback$,
    goals$: goals$,
    message$: message$,
    response$: response$,
    // stateId$: stateId$,
  };

}

function wrapAjax(i: JQueryAjaxSettings): Promise<any> {
  return new Promise((onFulfilled, onRejected) => {
    const jPromise = $.ajax(i);
    jPromise.done(o => onFulfilled(o));
    jPromise.fail(e => onRejected(e));
  });
}

function sendCommand(input: CoqtopInput.CoqtopInput): Promise<CoqtopOutput> {
  return new Promise((onFulfilled, onRejected) => {
    wrapAjax({
      type: 'POST',
      url: input.getCmd(),
      data: { data: JSON.stringify(input.getArgs()) },
      async: true,
      // error: e => console.log("Server did not respond", e),
      // success: r => console.log("Success", r, r[0].tag),
    })
      .then<CoqtopOutput>(r => ({
        response: $.extend(r[0], { input: input }),
        stateId: r[1][0],
        editId: r[1][1],
        messages: r[2][0],
        feedback: r[2][1],
      }))
      .then<void>(r => {
        if (r.response.tag === "ValueGood") {
          // console.log("onFulfilled", r);
          onFulfilled(r);
        } else if (r.response.tag === "ValueFail") {
          // console.log("onRejected", r);
          onRejected(r);
        } else {
          debugger;
        }
      });
  });
}

function processCommands(input$: Rx.Observable<CoqtopInput.CoqtopInput>): Rx.Observable<CoqtopOutput> {
  return input$.flatMap(i => sendCommand(i));
}
