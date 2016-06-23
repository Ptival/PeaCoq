import * as Answer from "./sertop/answer";
import * as AnswerKind from "./sertop/answer-kind";
import * as Command from "./sertop/command";
import * as Feedback from "./coq/feedback";
import * as FeedbackContent from "./coq/feedback-content";

export function setupCommunication(
  cmd$: Rx.Observable<Command.Command>
): CoqtopOutputStreams {
  const output$ = cmd$
    .concatMap(sendCommand)
    .concatMap(a => a)
    .share();
  output$.subscribe(_ => {}); // to keep it rolling for now
  const answer$: Rx.Observable<Sertop.IAnswer<Sertop.IAnswerKind>> =
    <Rx.Observable<any>>
    output$.filter(a => a instanceof Answer.Answer);
  const feedback$: Rx.Observable<IFeedback<IFeedbackContent>> =
    <Rx.Observable<any>>
    output$.filter(a => a instanceof Feedback.Feedback);
  return {
    answer$s: {
      coqExn$: answer$.filter<Sertop.IAnswer<Sertop.ICoqExn>>(a => a.answer instanceof AnswerKind.CoqExn),
      stmAdded$: answer$.filter<Sertop.IAnswer<Sertop.IStmAdded>>(a => a.answer instanceof AnswerKind.StmAdded),
    },
    feedback$s: {
      processed$: feedback$.filter(f => f.feedbackContent instanceof FeedbackContent.Processed),
    },
  };
}

function wrapAjax(i: JQueryAjaxSettings): Promise<any> {
  return new Promise((onFulfilled, onRejected) => {
    const jPromise = $.ajax(i);
    jPromise.done(o => onFulfilled(o));
    jPromise.fail(e => onRejected(e));
  });
}

function sendCommand(cmd: Sertop.ICmd): Promise<Sertop.IAnswer<Sertop.IAnswerKind>[]> {
  return new Promise((onFulfilled, onRejected) =>
    wrapAjax({
      type: "POST",
      url: "coqtop",
      data: { data: JSON.stringify(`(${cmd.tag} ${cmd.toSexp()})`) },
      async: true,
      // error: e => console.log("Server did not respond", e),
      // success: r => console.log("Success", r, r[0].tag),
    })
      .then(r => onFulfilled(_(r).map(sexpParse).map(Answer.create).value()))
  );
}
