
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
  responseStream: Rx.Observable<CoqtopResponse>;
  goodResponseStream: Rx.Observable<CoqtopResponse>;
  failResponseStream: Rx.Observable<CoqtopResponse>;
  stateIdStream: Rx.Observable<number>;
}

function setupCoqtopCommunication(
  inputs: Rx.Observable<CoqtopInput>[]
): CoqtopOutputStreams {

  let coqtopAddPrimeStream: Rx.Observable<CoqtopInput> =
    Rx.Observable
      .from([
        "Theorem test: forall (x: nat), 0 = 0.",
        "Proof.",
        "intros.",
        "reflexivity.",
        "Qed.",
      ])
      .map((s) => ({ cmd: "add'", args: s }))
    ;

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
      coqtopAddPrimeStream,
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
  // coqtopOutputStream.subscribe((x) => { console.log(x); });

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
  // coqtopStateIdStream.subscribe(
  //   (sid) => { console.log("State ID", sid); }
  // );

  let coqtopMessagesStream = coqtopOutputStream.flatMap((r) => r.messages);
  // coqtopMessagesStream.subscribe(
  //   (m) => { console.log("Message", new Message(m)); }
  // );

  let coqtopFeedbackStream = coqtopOutputStream.flatMap((r) => r.feedback);
  coqtopFeedbackStream.subscribe(
    (f) => { console.log("Feedback", new Feedback(f)); }
  );

  coqtopOutputStream.connect();

  return {
    responseStream: coqtopResponseStream,
    goodResponseStream: coqtopGoodResponseStream,
    failResponseStream: coqtopFailResponseStream,
    stateIdStream: coqtopStateIdStream,
  };

}
