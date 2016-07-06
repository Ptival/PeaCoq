import * as Answer from "./sertop/answer";
import * as AnswerKind from "./sertop/answer-kind";
import * as Command from "./sertop/command";
import * as ControlCommand from "./sertop/control-command";
import * as Feedback from "./coq/feedback";
import * as FeedbackContent from "./coq/feedback-content";
import * as MessageLevel from "./coq/message-level";

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
  const answer$ =
    output$.filter<Sertop.IAnswer<Sertop.IAnswerKind>>(a => a instanceof Answer.Answer);
  const feedback$ =
    output$.filter<IFeedback<IFeedbackContent>>(a => a instanceof Feedback.Feedback);
  const messageFeedback$ =
    feedback$.filter<MessageFeedback<IMessageLevel>>(a => a.feedbackContent instanceof FeedbackContent.Message);
  return {
    answer$s: {
      coqExn$: answer$.filter<Sertop.IAnswer<Sertop.ICoqExn>>(a => a.answer instanceof AnswerKind.CoqExn),
      stmAdded$: answer$.filter<Sertop.IAnswer<Sertop.IStmAdded>>(a => a.answer instanceof AnswerKind.StmAdded),
      stmCanceled$: answer$.filter<Sertop.IAnswer<Sertop.IStmCanceled>>(a => a.answer instanceof AnswerKind.StmCanceled),
    },
    feedback$s: {
      message$s: {
        debug$: messageFeedback$.filter<DebugMessageFeedback>(f => f.feedbackContent.level instanceof MessageLevel.Debug),
        error$: messageFeedback$.filter<ErrorMessageFeedback>(f => f.feedbackContent.level instanceof MessageLevel.Error),
        info$: messageFeedback$.filter<InfoMessageFeedback>(f => f.feedbackContent.level instanceof MessageLevel.Info),
        notice$: messageFeedback$.filter<NoticeMessageFeedback>(f => f.feedbackContent.level instanceof MessageLevel.Notice),
        warning$: messageFeedback$.filter<WarningMessageFeedback>(f => f.feedbackContent.level instanceof MessageLevel.Warning),
      },
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
  console.log(cmd);
  return wrapAjax({
    type: "POST",
    url: "coqtop",
    data: { data: JSON.stringify(`(${cmd.tag} ${cmd.toSexp()})`) },
    async: true,
  }).then(r => _(r).map(sexpParse).map(Answer.create).value());
}
