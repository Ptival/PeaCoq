import * as Command from "../sertop/command"
import * as ControlCommand from "../sertop/control-command"

// For now, if we don't remove the sentences immediately, when the user does
// Next right after editing somewhere, the Next grabs the sentence after the
// old tip, because the new tip has not registered yet. As a bad optimization,
// we drop all sentences beyond the change immediately. This will be incorrect
// when the user is allowed to edit within blocks.

export function setup(
  doc: ICoqDocument
): void {
  // Minor bug: this sends two Cancel commands when the user hits Enter
  // and Ace proceeds to insert a tabulation (these count as two changes)
  // The second Cancel is acknowledged by coqtop with no further action.
  doc.editorChange$
    .flatMap<ISentence<IStage>>(change =>
      doc.getSentenceAtPosition(minPos(change.start, change.end)).caseOf({
        nothing: () => [],
        just: s => [s],
      })
    )
    .do(sRemoved => doc.removeSentences(s => s.sentenceId >= sRemoved.sentenceId))
    .flatMap(s =>
      s.getStateId()
        .caseOf({
          nothing: () => [],
          just: sid => [Rx.Observable.just(new Command.Control(new ControlCommand.StmCancel([sid])))],
        })
    )
    .subscribe(cmd$ => doc.sendCommands(cmd$))
}

function minPos(pos1: AceAjax.Position, pos2: AceAjax.Position): AceAjax.Position {
  if (pos1.row < pos2.row) {
    return pos1
  }
  if (pos2.row < pos1.row) {
    return pos2
  }
  if (pos1.column < pos2.column) {
    return pos1
  }
  return pos2
}
