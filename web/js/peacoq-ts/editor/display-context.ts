import * as Command from "../sertop/command";
import * as ControlCommand from "../sertop/control-command";
import { isBefore } from "./editor-utils";
import * as DebugFlags from "../debug-flags";
import { Strictly } from "../strictly";

export function setup(
  doc: ICoqDocument,
  sentenceToDisplay$: Rx.Observable<ISentence<IStage>>
): Rx.Observable<Rx.Observable<Command.Control<ISertop.IControlCommand.IStmObserve>>> {

  const editor = doc.editor;

  // For each sentence we intend to display we must:

  // 1. listen to its context being ready, and display it when it is
  sentenceToDisplay$
    .concatMap(sentence => sentence.getProcessedStage())
    .concatMap(stage => stage.getContext())
    .subscribe(context => doc.contextPanel.display(context));

  // 2. send an Observe command to coqtop so that the context gets evaluated
  const stmObserve$: Rx.Observable<Rx.Observable<Command.Control<ISertop.IControlCommand.IStmObserve>>> =
    sentenceToDisplay$
      .flatMap(s => s.getBeingProcessed$())
      .map(bp => Rx.Observable.just(new Command.Control(new ControlCommand.StmObserve(bp.stateId))))
      .share();

  return stmObserve$;

}
