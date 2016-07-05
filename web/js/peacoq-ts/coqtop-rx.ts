import * as DebugFlags from "./debug-flags";
import { Feedback } from "./coq/feedback";
import * as FeedbackContent from "./coq/feedback-content";
import { ValueFail } from "./coq/value-fail";
import * as CoqtopInput from "./coqtop-input";
import { processSequentiallyForever } from "./rx";

let statusPeriod = 10000; // milliseconds
//
// export function setupCoqtopCommunication(
//   input$s: Rx.Observable<ICoqtopInput>[]
// ): CoqtopOutputStreams {
//
//   let inputStatus$: Rx.Observable<ICoqtopInput> =
//     Rx.Observable
//       .interval(statusPeriod)
//       .map(() => new CoqtopInput.Status(false));
//
//   let inputSubject: Rx.Subject<ICoqtopInput> =
//     new Rx.Subject<ICoqtopInput>();
//
//   let input$: Rx.ConnectableObservable<ICoqtopInput> =
//     Rx.Observable
//       .merge(
//       inputStatus$,
//       inputSubject.asObservable(),
//       ...input$s
//       )
//       .publish();
//
//   // subscribeAndLog(coqtopInputStream);
//
//   let outputAndError$s = processSequentiallyForever(input$, processCommands);
//
//   const io$ = outputAndError$s.output$;
//
//   // const error$ = outputAndError$s.error$
//   //   .map(r => {
//   //     return new ValueFail(r.response.contents);
//   //   })
//   //   .share();
//
//   // error$.subscribe(vf => inputSubject.onNext(new CoqtopInput.EditAt(vf.stateId)));
//
//   if (DebugFlags.requestToCoqtop) {
//     input$
//       .filter(i => !(i instanceof CoqtopInput.Status))
//       .subscribe(input => { console.log("⟸", input); });
//   }
//   if (DebugFlags.responseFromCoqtop) {
//     io$
//       .filter(io => !(io.input instanceof CoqtopInput.Status))
//       .subscribe(io => { console.log("   ⟹", io.input, io.output); });
//   }
//   // if (DebugFlags.errorFromCoqtop) {
//   //   error$
//   //     .subscribe(vf => { console.log("   ⟹ ERROR", vf); });
//   // }
//
//   let message$: Rx.Observable<IMessage> =
//     io$
//       .concatMap(io => _(io.output.messages).map(m => new Message(m)).value())
//       .share();
//   if (DebugFlags.messageFromCoqtop) {
//     message$.subscribe(m => console.log("Message", m));
//   }
//
//   /* IMPORTANT: It is important to process Feedback messages before
//   processing the output value, because a ValueFail may refer to state
//   IDs that are only present in the current output's feedback. We
//   artificially delay the output value stream to achieve this easily. */
//
//   const feedback$: Rx.Subject<IFeedback<IFeedbackContent>> = new Rx.Subject<IFeedback<IFeedbackContent>>();
//   const value$: Rx.Subject<ICoqtopResponse<any>> = new Rx.Subject<any>();
//
//   io$.subscribe(io => {
//     Rx.Observable.fromArray(_(io.output.feedback).map(f => new Feedback(f)).value())
//       .subscribe(f => feedback$.onNext(f));
//     // console.log("All feedbacks should have been processed, now pushing return value");
//     value$.onNext(io.output.response);
//   });
//   if (DebugFlags.feedbackFromCoqtop) {
//     feedback$
//       .distinctUntilChanged() // so redundant when calling status
//       .subscribe(f => console.log("Feedback", f));
//   }
//
//   // this is needed for PeaCoq because we use add' so the STM's state
//   // needs to be put back to where it worked
//   // TODO: make a config flag for this feature
//   // error$.subscribe(e => {
//     // console.log("sending EditAt because of error");
//   //   inputSubject.onNext(new CoqtopInput.EditAt(e.stateId));
//   // });
//
//   // let addResponse$: Rx.Observable<AddReturn> =
//   //   response$
//   //     .filter(r => r.input instanceof CoqtopInput.AddPrime)
//   //     .map(r => ({
//   //       stateId: r.contents[0],
//   //       eitherNullStateId: r.contents[1][0],
//   //       output: r.contents[1][1],
//   //     }))
//   //   ;
//
//   // let stateId$ = output$.map(r => r.stateId);
//
//   input$.connect();
//
//   const [goodResponse$, badResponse$] = io$.partition(o => o.output.response.tag === "ValueGood");
//
//   return {
//     input$: input$,
//     // io$: io$,
//     // error$: error$,
//     feedback$s: {
//       addedAxiom$: <any>(feedback$.filter(f => f.feedbackContent instanceof FeedbackContent.AddedAxiom)),
//       errorMsg$: <any>feedback$.filter(f => f.feedbackContent instanceof FeedbackContent.ErrorMsg),
//       fileDependency$: <any>feedback$.filter(f => f.feedbackContent instanceof FeedbackContent.FileDependency),
//       fileLoaded$: <any>feedback$.filter(f => f.feedbackContent instanceof FeedbackContent.FileLoaded),
//       processed$: <any>feedback$.filter(f => f.feedbackContent instanceof FeedbackContent.Processed),
//       processingIn$: <any>feedback$.filter(f => f.feedbackContent instanceof FeedbackContent.ProcessingIn),
//     },
//     feedback$: feedback$,
//     message$: message$,
//     valueFail$: badResponse$.map(x => new ValueFail(x.output.response.contents)),
//     valueGood$s: {
//       add$: goodResponse$.filter(r => r.input instanceof CoqtopInput.AddPrime),
//       editAt$: goodResponse$.filter(r => r.input instanceof CoqtopInput.EditAt),
//     },
//     // stateId$: stateId$,
//   };
//
// }
//
// function wrapAjax(i: JQueryAjaxSettings): Promise<any> {
//   return new Promise((onFulfilled, onRejected) => {
//     const jPromise = $.ajax(i);
//     jPromise.done(o => onFulfilled(o));
//     jPromise.fail(e => onRejected(e));
//   });
// }
//
// function sendCommand<I extends ICoqtopInput>(input: I): Promise<ICoqtopOutput<I, any>> {
//   return new Promise((onFulfilled, onRejected) => {
//     wrapAjax({
//       type: "POST",
//       url: "coqtop",
//       data: { data: JSON.stringify(input.getCmd()) },
//       async: true,
//       // error: e => console.log("Server did not respond", e),
//       // success: r => console.log("Success", r, r[0].tag),
//     })
//       .then<ICoqtopOutput<I, any>>(r => ({
//         input: input,
//         output: _(r).map(sexpParse).map(mkAnswer).value()
//       }))
//       .then(r => {
//         debugger;
//         if (input.callback !== undefined) {
//           input.callback(r);
//         }
//         onFulfilled(r);
//       });
//   });
// }
//
// function processCommands<I extends ICoqtopInput>(input$: Rx.Observable<I>): Rx.Observable<{ continue: boolean, output: ICoqtopOutput<I, any> }> {
//   return input$
//     .concatMap(i => sendCommand(i))
//     .map(io => ({ continue: io.output.response.tag === "ValueGood", output: io }))
//     ;
// }
