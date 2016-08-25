export function setup(
  tip$: Rx.Observable<Tip>
) {
  tip$
    .filter(isJust)
    .map(fromJust)
    .concatMap((s: ISentence<IStage>) => s.completionAdded$)
    .subscribe(x => {

    });
}
