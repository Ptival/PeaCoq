import * as Command from "../sertop/command";
import * as ControlCommand from "../sertop/control-command";
import { isBefore } from "./editor-utils";
import * as DebugFlags from "../debug-flags";
import { Strictly } from "../strictly";

export function setup(
  doc: ICoqDocument
): Rx.Observable<Rx.Observable<Command.Control<ISertop.IControlCommand.IStmObserve>>> {
  const editor = doc.editor;

  const textCursorChangeEvent$ = Rx.Observable
    .create(observer => editor.selection.on("changeCursor", e => observer.onNext(e)))
    .share();

  const textCursorPosition$ = textCursorChangeEvent$
    .map(() => editor.selection.getCursor())
    .share();
  if (DebugFlags.textCursorPosition) { subscribeAndLog(textCursorPosition$); }

  const sentenceToBeDisplayed$: Rx.Observable<ISentence<IStage>> =
    textCursorPosition$
      .debounce(250)
      .flatMap(pos => {
        // we want to display the last sentence whose stopPos is before `pos`
        const sentence = _(doc.getAllSentences())
          .findLast(s => isBefore(Strictly.No, s.stopPosition, pos));
        return sentence ? [sentence] : [];
      })
      .distinctUntilChanged()
      .share();
  if (DebugFlags.sentenceToBeDisplayed) { subscribeAndLog(sentenceToBeDisplayed$); }

  sentenceToBeDisplayed$
    .flatMap(sentence => sentence.getProcessedStage())
    .flatMap(stage => stage.getContext())
    .subscribe(context => doc.contextPanel.display(context));

  const stmObserve$: Rx.Observable<Rx.Observable<Command.Control<ISertop.IControlCommand.IStmObserve>>> =
    sentenceToBeDisplayed$
      .flatMap(s => s.getBeingProcessed$())
      .map(bp => Rx.Observable.just(new Command.Control(new ControlCommand.StmObserve(bp.stateId))))
      .share();

  return stmObserve$;

}
