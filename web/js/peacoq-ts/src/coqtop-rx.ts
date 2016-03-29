
interface CoqtopInput {
  cmd: string;
  args: Object;
}

interface CoqtopResponse {
  input: CoqtopInput;
  tag: string;
  contents: Object;
}

interface CoqtopOutput {
  response: CoqtopResponse;
  stateId: number;
  editId: number;
  messages: Object[];
  feedback: Object[];
}

interface CoqtopOutputStreams {
  failResponse: Rx.Observable<CoqtopResponse>;
  feedback: Rx.Observable<Feedback>;
  goodResponse: Rx.Observable<CoqtopResponse>;
  messages: Rx.Observable<Message>;
  response: Rx.Observable<CoqtopResponse>;
  stateId: Rx.Observable<number>;
}

function setupCoqtopCommunication(
  inputs: Rx.Observable<CoqtopInput>[]
): CoqtopOutputStreams {

  let coqtopEditAtStream: Rx.Observable<CoqtopInput> =
    Rx.Observable.empty<CoqtopInput>();

  let coqtopStatusStream: Rx.Observable<CoqtopInput> =
    Rx.Observable
      .interval(2000)
      .map(() => ({ cmd: "status", args: false }))
    ;

  let coqtopInputStream: Rx.Observable<CoqtopInput> =
    Rx.Observable
      .merge(
      // coqtopStatusStream,
      ...inputs
      )
      .startWith({ cmd: "editat", args: 1 })
    // .concat(Rx.Observable.return({ cmd: "quit", args: [] }))
    ;

  coqtopInputStream.subscribe((input) => {
    console.log("coqtop ⟸ ", input);
  });

  let coqtopOutputStream: Rx.ConnectableObservable<CoqtopOutput> =
    coqtopInputStream
      .flatMap((input) => {
        return Rx.Observable
          .fromPromise($.ajax({
            type: 'POST',
            url: input.cmd,
            data: { data: JSON.stringify(input.args) },
            async: true,
            error: () => { console.log("Server did not respond!"); },
            // success: (response) => { console.log("SUCCESS", input); },
          }))
          .map((r) => ({
            response: $.extend(r[0], { input: input }),
            stateId: r[1][0],
            editId: r[1][1],
            messages: r[2][0],
            feedback: r[2][1],
          }))
          ;
      })
      .publish()
    ;
  coqtopOutputStream.connect();

  let coqtopResponseStream = coqtopOutputStream.map((r) => r.response);
  coqtopResponseStream.subscribe(
    (r) => { console.log("coqtop ⟹ ", r.input, r.contents); }
  );

  let coqtopGoodResponseStream =
    coqtopResponseStream.filter((r) => r.tag === "ValueGood")
    ;

  let coqtopFailResponseStream =
    coqtopResponseStream.filter((r) => r.tag === "ValueFail")
    ;

  let coqtopAddResponseStream: Rx.Observable<AddReturn> =
    coqtopGoodResponseStream
      .filter((r) => r.input.cmd === "add'")
      .map((r) => ({
        stateId: r.contents[0],
        eitherNullStateId: r.contents[1][0],
        output: r.contents[1][1],
      }))
    ;

  let coqtopStateIdStream = coqtopOutputStream.map((r) => r.stateId);

  let coqtopMessagesStream: Rx.Observable<Message> =
    coqtopOutputStream.flatMap(
      (r) => _(r.messages).map((m) => new Message(m)).value()
    );

  let coqtopFeedbackStream: Rx.Observable<Feedback> =
    coqtopOutputStream.flatMap(
      (r) => _(r.feedback).map((f) => new Feedback(f)).value()
    );

  return {
    failResponse: coqtopFailResponseStream,
    feedback: coqtopFeedbackStream,
    goodResponse: coqtopGoodResponseStream,
    messages: coqtopMessagesStream,
    response: coqtopResponseStream,
    stateId: coqtopStateIdStream,
  };

}
