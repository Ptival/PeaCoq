import * as DebugFlags from "./debug-flags";
import { Feedback } from "./coq/feedback";
import { Message } from "./coq/message";
import { ValueFail } from "./coq/value-fail";
import * as CoqtopInput from "./coqtop-input";
import { processSequentiallyForever } from "./rx";

let statusPeriod = 250; // milliseconds

interface CoqtopOutputStreams {
  error$: Rx.Observable<ValueFail>;
  feedback$: Rx.Observable<IFeedback>;
  response$: Rx.Observable<ICoqtopResponse<ICoqtopInput, any>>;
  message$: Rx.Observable<IMessage>;
  // stateId$: Rx.Observable<number>;
}

export function setupCoqtopCommunication(
  input$s: Rx.Observable<ICoqtopInput>[]
): CoqtopOutputStreams {

  let inputStatus$: Rx.Observable<ICoqtopInput> =
    Rx.Observable
      .interval(statusPeriod)
      .map(() => new CoqtopInput.Status(false));

  let inputSubject: Rx.Subject<ICoqtopInput> =
    new Rx.Subject<ICoqtopInput>();

  let input$: Rx.ConnectableObservable<ICoqtopInput> =
    Rx.Observable
      .merge(
      inputStatus$,
      inputSubject.asObservable(),
      ...input$s
      )
      .publish();

  // subscribeAndLog(coqtopInputStream);

  let outputAndError$s = processSequentiallyForever(input$, processCommands);
  const output$ = outputAndError$s.output$;
  const error$ = outputAndError$s.error$
    .map(r => {
      return new ValueFail(r.response.contents);
    })
    .share();
  error$.subscribe(vf => inputSubject.onNext(new CoqtopInput.EditAt(vf.stateId)));

  let response$ = output$.map(r => r.response);

  if (DebugFlags.requestToCoqtop) {
    input$
      .filter(i => !(i instanceof CoqtopInput.Status))
      .subscribe(input => { console.log("⟸", input); });
  }
  if (DebugFlags.responseFromCoqtop) {
    response$
      .filter(r => !(r.input instanceof CoqtopInput.Status))
      .subscribe(r => { console.log("   ⟹", r.input, r); });
  }
  if (DebugFlags.errorFromCoqtop) {
    error$
      .subscribe(vf => { console.log("   ⟹ ERROR", vf); });
  }

  // this is needed for PeaCoq because we use add' so the STM's state
  // needs to be put back to where it worked
  // TODO: make a config flag for this feature
  error$.subscribe(e => {
    // console.log("sending EditAt because of error");
    inputSubject.onNext(new CoqtopInput.EditAt(e.stateId));
  });

  // let addResponse$: Rx.Observable<AddReturn> =
  //   response$
  //     .filter(r => r.input instanceof CoqtopInput.AddPrime)
  //     .map(r => ({
  //       stateId: r.contents[0],
  //       eitherNullStateId: r.contents[1][0],
  //       output: r.contents[1][1],
  //     }))
  //   ;

  let stateId$ = output$.map(r => r.stateId);

  let message$: Rx.Observable<IMessage> =
    output$
      .flatMap(r => _(r.messages).map(m => new Message(m)).value())
      .share();
  if (DebugFlags.messageFromCoqtop) {
    message$.subscribe(m => console.log("Message", m));
  }

  let feedback$: Rx.Observable<IFeedback> =
    output$
      .flatMap(r => _(r.feedback).map(f => new Feedback(f)).value())
      .share();
  if (DebugFlags.feedbackFromCoqtop) {
    feedback$
      .distinctUntilChanged() // so redundant!
      .subscribe(f => console.log("Feedback", f));
  }

  input$.connect();

  return {
    error$: error$,
    feedback$: feedback$,
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

function sendCommand<I extends ICoqtopInput>(input: I): Promise<ICoqtopOutput<I, any>> {
  return new Promise((onFulfilled, onRejected) => {
    wrapAjax({
      type: 'POST',
      url: input.getCmd(),
      data: { data: JSON.stringify(input.getArgs()) },
      async: true,
      // error: e => console.log("Server did not respond", e),
      // success: r => console.log("Success", r, r[0].tag),
    })
      .then<ICoqtopOutput<I, any>>(r => ({
        response: $.extend(r[0], { input: input }),
        stateId: r[1][0],
        editId: r[1][1],
        messages: r[2][0],
        feedback: r[2][1],
      }))
      .then<void>(r => {
        if (r.response.tag === "ValueGood") {
          if (input.callback !== undefined) {
            input.callback(r.response);
          }
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

function processCommands<I extends ICoqtopInput>(input$: Rx.Observable<I>): Rx.Observable<ICoqtopOutput<I, any>> {
  return input$.flatMap(i => sendCommand(i));
}
