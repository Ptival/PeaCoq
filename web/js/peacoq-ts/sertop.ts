import * as Answer from "./sertop/answer";
import * as AnswerKind from "./sertop/answer-kind";
import * as Command from "./sertop/command";
import * as ControlCommand from "./sertop/control-command";
import * as Feedback from "./coq/feedback";
import * as FeedbackContent from "./coq/feedback-content";
import * as MessageLevel from "./coq/message-level";

export function setupCommunication(
  cmd$: Rx.Observable<ISertop.ICommand>
): CoqtopOutputStreams {

  // Need to use something like websockets to avoid having to poll like this
  const pingOutput$ =
    Rx.Observable.interval(250)
      .concatMap(sendPing)
      .concatMap(a => a)
      .share();

  // This will contain a value every time we receive a response
  const cmdOutputSubject = new Rx.Subject<number>();

  // We must slow down cmd$ because server handlers are run in parallel
  // and writes to coqtop are not atomic, so burst of messages become
  // intertwined!...
  const slowedCmd$ =
    Rx.Observable.zip(
      cmd$,
      cmdOutputSubject
    );

  // cmdOutputSubject.subscribe(nb => console.log("ACK", nb));

  const cmdOutput$ =
    slowedCmd$
      .concatMap(([cmd, nb]) => {
        // console.log("SND", cmd.tag, cmd);
        return sendCommand(cmd);
      })
      .concatMap(a => a)
      .publish();

  const output$ = Rx.Observable.merge(pingOutput$, cmdOutput$);

  output$
    .filter(o => o instanceof Answer.Answer)
    .filter(o => o.answer instanceof AnswerKind.Ack)
    // we don't listen to the answer from `cmdTagMinimum` as it may not arrive
    .filter(o => + o.cmdTag >= Command.cmdTagMinimum + 1)
    .subscribe(o => { cmdOutputSubject.onNext(+ o.cmdTag); });

  cmdOutput$.connect();
  // So, this is a bit complicated, but we need two freebies:
  // - the first one is the command Quit, whose ACK we may or may not receive
  // - the second one is the first actualy command we care to send
  cmdOutputSubject.onNext(-2);
  cmdOutputSubject.onNext(-1);

  const answer$ =
    output$.filter<ISertop.IAnswer<ISertop.IAnswerKind>>(a => a instanceof Answer.Answer);
  const feedback$ =
    output$.filter<IFeedback<IFeedbackContent>>(a => a instanceof Feedback.Feedback);
  const messageFeedback$ =
    feedback$.filter<MessageFeedback<IMessageLevel>>(a => a.feedbackContent instanceof FeedbackContent.Message);
  return {
    answer$s: {
      completed$: answer$.filter<ISertop.IAnswer<ISertop.ICoqExn>>(a => a.answer instanceof AnswerKind.Completed),
      coqExn$: answer$.filter<ISertop.IAnswer<ISertop.ICoqExn>>(a => a.answer instanceof AnswerKind.CoqExn),
      stmAdded$: answer$.filter<ISertop.IAnswer<ISertop.IStmAdded>>(a => a.answer instanceof AnswerKind.StmAdded),
      stmCanceled$: answer$.filter<ISertop.IAnswer<ISertop.IStmCanceled>>(a => a.answer instanceof AnswerKind.StmCanceled),
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

function sendPing(): Promise<ISertop.IAnswer<ISertop.IAnswerKind>[]> {
  // console.log("PING");
  return wrapAjax({
    type: "POST",
    url: "ping",
    data: {},
    async: true,
  }).then(r => _(r).map(sexpParse).map(Answer.create).value());
}

function sendCommand(cmd: ISertop.ICommand): Promise<ISertop.IAnswer<ISertop.IAnswerKind>[]> {
  // console.log("SEND", cmd);
  return wrapAjax({
    type: "POST",
    url: "coqtop",
    data: { data: JSON.stringify(`(${cmd.tag} ${cmd.toSexp()})`) },
    async: true,
  }).then(r => {
    // console.log("RECV", r);
    return _(r).map(sexpParse).map(Answer.create).value();
  });
}
