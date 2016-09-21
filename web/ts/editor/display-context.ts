import { setup as setupSentenceToDisplay } from "./sentence-to-display"
import * as Command from "../sertop/command"
import * as ControlCommand from "../sertop/control-command"
import { isBefore } from "./editor-utils"
import * as DebugFlags from "../peacoq/debug-flags"
import { Strictly } from "../peacoq/strictly"

export function setup(
  doc: ICoqDocument
): void {

  const sentenceToDisplay$ = setupSentenceToDisplay(doc)

  // For each sentence we intend to display we must:

  // 1. listen to its context being ready, and display it when it is
  sentenceToDisplay$
    // .do(s => console.log("I want to display", s))
    .concatMap(sentence => sentence.getProcessed$())
    // .do(s => console.log("I waited for it to be processed", s))
    .concatMap(stage => stage.getContext())
    // .do(s => console.log("I waited for its context", s))
    .subscribe(context => doc.contextPanel.display(context))

  // 2. send an Observe command to coqtop so that the context gets evaluated
  sentenceToDisplay$
    .flatMap(s => s.getBeingProcessed$())
    .map(bp => Rx.Observable.just(new Command.Control(new ControlCommand.StmObserve(bp.stateId))))
    .subscribe(cmd$ => doc.sendCommands(cmd$))

}
