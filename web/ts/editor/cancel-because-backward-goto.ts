import { Cancel } from "../sertop/serapi-protocol"

export function setup(
  doc : ICoqDocument,
  backwardGoTo$ : Rx.Observable<AceAjax.Position>
) : void {

  backwardGoTo$
    .flatMap(destinationPos => {
      const maybeSentence = doc.getSentenceAtPosition(destinationPos)
      return (
        maybeSentence
          .bind(e => e.getStateId())
          .fmap(s => new Cancel([s]))
          .caseOf({
            nothing : () => [],
            just : cmd => [Rx.Observable.just(cmd)],
          })
      )
    })
    .subscribe(cmd$ => doc.sendCommands(cmd$))

}
