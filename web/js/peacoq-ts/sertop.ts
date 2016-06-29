import * as Answer from "./sertop/answer";
import * as AnswerKind from "./sertop/answer-kind";
import * as Command from "./sertop/command";
import * as ControlCommand from "./sertop/control-command";
import * as Feedback from "./coq/feedback";
import * as FeedbackContent from "./coq/feedback-content";

export function setupCommunication(
  cmd$: Rx.Observable<Command.Command>
): CoqtopOutputStreams {
  // we issue a join every time the command stream becomes silent
  // const join$ = cmd$.debounce(1000).map(_ => new Command.Control(new ControlCommand.StmObserve()));
  const pingOutput$ =
    Rx.Observable.interval(250)
      .concatMap(sendPing)
      .concatMap(a => a)
      .share();
  const cmdOutput$ = Rx.Observable.merge(cmd$) //, join$)
    .concatMap(sendCommand)
    .concatMap(a => a)
    .share();
  const output$ = Rx.Observable.merge(pingOutput$, cmdOutput$);
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
      stmCanceled$: answer$.filter<Sertop.IAnswer<Sertop.IStmCanceled>>(a => a.answer instanceof AnswerKind.StmCanceled),
    },
    feedback$s: {
      errorMsg$: feedback$.filter<IFeedback<IFeedbackContent.IErrorMsg>>(f => f.feedbackContent instanceof FeedbackContent.ErrorMsg),
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

function sendPing(): Promise<Sertop.IAnswer<Sertop.IAnswerKind>[]> {
  return wrapAjax({
    type: "POST",
    url: "ping",
    data: {},
    async: true,
  }).then(r => _(r).map(sexpParse).map(Answer.create).value());
}

function sendCommand(cmd: Sertop.ICmd): Promise<Sertop.IAnswer<Sertop.IAnswerKind>[]> {
  return wrapAjax({
    type: "POST",
    url: "coqtop",
    data: { data: JSON.stringify(`(${cmd.tag} ${cmd.toSexp()})`) },
    async: true,
  }).then(r => _(r).map(sexpParse).map(Answer.create).value());
}
