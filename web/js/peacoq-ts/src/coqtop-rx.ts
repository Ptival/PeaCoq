import * as CoqtopInput from "./coqtop-input";
import { Feedback } from "./coq/feedback";
import { Goals } from "./goals";
import { Message } from "./coq/message";
import { ValueFail } from "./coq/value-fail";

let statusPeriod = 2500; // milliseconds

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

interface CoqtopError {
  errorMessage: string;
  errorStart: number;
  errorStop: number;
  stateId: number;
}

interface CoqtopOutputStreams {
  error$: Rx.Observable<CoqtopError>;
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
      inputSubject,
      ...input$s
      )
      .publish();

  // subscribeAndLog(coqtopInputStream);

  let errorSubject = new Rx.Subject<CoqtopError>();
  let error$ = errorSubject.asObservable();

  /*
  Note: the scan has two effects
  1. it ensures AJAX requests reach the server in order of emission
  2. the current backend does not sequence requests, which causes issues
     when sending multiple add requests even in the absence of network
     reordering. the issue is that the server fills in stateIds, and if
     it receives two adds and processes the second immediately, it will
     add to the old stateId rather than the once produced by the first add.
  */
  let output$: Rx.Observable<CoqtopOutput> =
    processInput$(input$)
      .catch((r) => {
        const [stateId, [errorStart, errorStop], errorMessage] = r.response.contents;
        errorSubject.onNext({
          errorMessage: unbsp(errorMessage),
          errorStart: errorStart,
          errorStop: errorStop,
          stateId: stateId,
        });
        return processInput$(input$);
      })
      .share();

  error$.subscribe((e) => console.log("error", e));

  let response$ = output$.map((r) => r.response);

  input$
    .filter((i) => !(i instanceof CoqtopInput.Status))
    .subscribe((input) => { console.log("⟸", input); });
  response$
    .filter((r) => !(r.input instanceof CoqtopInput.Status))
    .subscribe((r) => { console.log("   ⟹", r.input, r.contents); });

  // this is needed for PeaCoq because we use add' so the STM's state
  // needs to be put back to where it worked
  // TODO: make a config flag for this feature
  error$.subscribe(e => {
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

function processInput$(input$: Rx.Observable<CoqtopInput.CoqtopInput>): Rx.Observable<CoqtopOutput> {
  return input$
    .concatMap(input => {
      return $.ajax({
        type: 'POST',
        url: input.getCmd(),
        data: { data: JSON.stringify(input.getArgs()) },
        async: true,
        error: e => console.log("Server did not respond"),
        //success: () => console.log("Success"),
      })
        .then<CoqtopOutput>(r => ({
          response: $.extend(r[0], { input: input }),
          stateId: r[1][0],
          editId: r[1][1],
          messages: r[2][0],
          feedback: r[2][1],
        }));
    })
    // dealing with errors in the jQuery promise is annoying because
    // it's not compliant to standards, and the console freaks out
    // and reports errors even though I catch them later, so I deal
    // with them here with Observables
    .concatMap(r => {
      if (r.response.tag === "ValueFail") {
        return Rx.Observable.throw<CoqtopOutput>(r);
      } else {
        return Rx.Observable.return(r);
      }
    })
}
