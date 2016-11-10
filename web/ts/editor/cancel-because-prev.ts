import * as _ from "lodash"

import * as Command from "../sertop/command"
import * as ControlCommand from "../sertop/control-command"

export function setup(
  doc: ICoqDocument,
  prev$: Rx.Observable<{}>
): void {

  const sentenceToCancelBecausePrev$: Rx.Observable<ISentence<IStage>> =
    prev$
      .flatMap(({}) => {
        if (doc.getSentencesToProcess().length > 0) { return [] }
        return [_.maxBy(doc.getAllSentences(), s => s.sentenceId)]
      })
      .share()

  sentenceToCancelBecausePrev$.subscribe(s => {
    doc.moveCursorToPositionAndCenter(s.startPosition)
  })

  sentenceToCancelBecausePrev$
    .flatMap(s =>
      s.getStateId().caseOf({
        nothing: () => [],
        just: sid => [sid],
      })
    )
    .map(sid => Rx.Observable.just(new Command.Control(new ControlCommand.StmCancel([sid]))))
    .subscribe(cmd$ => doc.sendCommands(cmd$))

}
