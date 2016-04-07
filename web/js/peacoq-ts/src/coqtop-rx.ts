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

interface CoqtopOutputStreams {
  failResponse: Rx.Observable<IValueFail>;
  feedback: Rx.Observable<IFeedback>;
  goal: Rx.Observable<Goals>;
  goodResponse: Rx.Observable<CoqtopResponse>;
  messages: Rx.Observable<IMessage>;
  response: Rx.Observable<CoqtopResponse>;
  stateId: Rx.Observable<number>;
}

export function setupCoqtopCommunication(
  inputs: Rx.Observable<CoqtopInput.CoqtopInput>[]
): CoqtopOutputStreams {

  let coqtopEditAtStream: Rx.Observable<CoqtopInput.CoqtopInput> =
    Rx.Observable.empty<CoqtopInput.CoqtopInput>();

  let coqtopStatusStream: Rx.Observable<CoqtopInput.CoqtopInput> =
    Rx.Observable
      .interval(statusPeriod)
      .map(() => new CoqtopInput.Status(false));

  let inputSubject: Rx.Subject<CoqtopInput.CoqtopInput> = new Rx.Subject<CoqtopInput.CoqtopInput>();

  let coqtopInputStream: Rx.Observable<CoqtopInput.CoqtopInput> =
    Rx.Observable
      .merge(
      coqtopStatusStream,
      inputSubject,
      ...inputs
      );

  /*
  Note: the scan has two effects
  1. it ensures AJAX requests reach the server in order of emission
  2. the current backend does not sequence requests, which causes issues
     when sending multiple add requests even in the absence of network
     reordering. the issue is that the server fills in stateIds, and if
     it receives two adds and processes the second immediately, it will
     add to the old stateId rather than the once produced by the first add.
  */
  let coqtopOutputStream: Rx.Observable<CoqtopOutput> =
    coqtopInputStream
      .scan<Promise<any>>((acc: Promise<any>, input: CoqtopInput.CoqtopInput) => {
        return acc
          .then(() => $.ajax({
            type: 'POST',
            url: input.getCmd(),
            data: { data: JSON.stringify(input.getArgs()) },
            async: true,
            error: () => console.log("Server did not respond!"),
            //success: () => console.log("Success"),
          }))
          .then<CoqtopOutput>((r) => ({
            response: $.extend(r[0], { input: input }),
            stateId: r[1][0],
            editId: r[1][1],
            messages: r[2][0],
            feedback: r[2][1],
          }));
      }, Promise.resolve())
      .flatMap((x) => x)
      .share()
    ;

  let coqtopResponseStream = coqtopOutputStream.map((r) => r.response);

  // coqtopInputStream
  //   .filter((i) => !(i instanceof CoqtopInput.Status))
  //   .filter((i) => !(i instanceof CoqtopInput.QueryPrime))
  //   .subscribe((input) => { console.log("⟸", input); });
  // coqtopResponseStream
  //   .filter((r) => !(r.input instanceof CoqtopInput.Status))
  //   .filter((r) => !(r.input instanceof CoqtopInput.QueryPrime))
  //   .subscribe((r) => { console.log("   ⟹", r.input, r.contents); });

  let coqtopGoodResponseStream =
    coqtopResponseStream.filter((r) => r.tag === "ValueGood")
    ;

  let coqtopFailResponseStream: Rx.Observable<IValueFail> =
    coqtopResponseStream
      .filter((r) => r.tag === "ValueFail")
      .map((r) => new ValueFail(r.contents))
    ;

  coqtopFailResponseStream.subscribe((vf) => {
    inputSubject.onNext(new CoqtopInput.EditAt(vf.stateId));
  })

  let coqtopAddResponseStream: Rx.Observable<AddReturn> =
    coqtopGoodResponseStream
      .filter((r) => r.input instanceof CoqtopInput.AddPrime)
      .map((r) => ({
        stateId: r.contents[0],
        eitherNullStateId: r.contents[1][0],
        output: r.contents[1][1],
      }))
    ;

  let coqtopStateIdStream = coqtopOutputStream.map((r) => r.stateId);

  let coqtopMessagesStream: Rx.Observable<IMessage> =
    coqtopOutputStream
      .flatMap((r) => _(r.messages).map((m) => new Message(m)).value())
      .share();

  let coqtopFeedbackStream: Rx.Observable<IFeedback> =
    coqtopOutputStream
      .flatMap((r) => _(r.feedback).map((f) => new Feedback(f)).value())
      .share();

  let coqtopGoalStream: Rx.Observable<Goals> =
    coqtopGoodResponseStream
      .filter((r) => r.input instanceof CoqtopInput.Goal)
      .filter((r) => r.contents !== null)
      .map((r) => new Goals(r.contents));

  return {
    failResponse: coqtopFailResponseStream,
    feedback: coqtopFeedbackStream,
    goal: coqtopGoalStream,
    goodResponse: coqtopGoodResponseStream,
    messages: coqtopMessagesStream,
    response: coqtopResponseStream,
    stateId: coqtopStateIdStream,
  };

}
