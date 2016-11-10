import * as _ from "lodash"

export function setup(
  doc: ICoqDocument,
  tip$: Rx.Observable<Tip>
) {
  tip$
    .filter(isJust)
    .map(fromJust)
    .flatMapLatest(s => s.waitUntilProcessed())
    .flatMapLatest(s => s.completionAdded$.map(() => s))
    .subscribe(s => {
      const stateId = s.stage.stateId
      doc.getActiveProofTree().fmap(pt => {
        const curNode = pt.curNode
        if (_(curNode.getStateIds()).includes(stateId)) {
          for (const groupName in s.completions) {
            const group = s.completions[groupName]
            for (const tactic in s.completions[groupName]) {
              const completion = group[tactic]
              curNode.addTactic(tactic, groupName, completion, stateId)
              pt.scheduleUpdate()
            }
          }
        } else {
          console.log("Curnode did not match stateID", stateId, curNode.getStateIds())
        }
      })
    })
}
