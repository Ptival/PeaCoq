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
      const stateId = s.stage.stateId;
      doc.getActiveProofTree().fmap(pt => {
        const curNode = pt.curNode;
        if (_(curNode.getStateIds()).includes(stateId)) {
          console.log("Curnode matches stateID, ready to add completions");
        } else {
          console.log("Curnode did not match stateID", stateId, curNode.getStateIds());
        }
      });
    });
}
