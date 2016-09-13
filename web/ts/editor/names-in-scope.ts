import { namesInScopeRoute } from "../peacoq/routes";
import { Control } from "../sertop/command";
import { StmAdd, StmEditAt, StmQuery } from "../sertop/control-command";

export function setup(
  doc: ICoqDocument,
  notice$: Notice$
): Rx.Observable<string[]> {
  doc.debouncedTip$
    .map(tip => {
      return tip
        .bind(t => t.stage.getStateId())
        .caseOf({
          nothing: () => Rx.Observable.empty<ISertop.ICommand>(),
          just: sid => {
            const set = new Control(new StmAdd({}, "Set Search Output Name Only.", true));
            const search = new Control(new StmQuery({ route: namesInScopeRoute }, `SearchAbout -"PEACOQ_NAMES_IN_SCOPE".`, true));
            const editAt = new Control(new StmEditAt(sid));
            return Rx.Observable.of<ISertop.ICommand>(set, search, editAt);
          }
        })
    })
    .subscribe(cmd$ => doc.sendCommands(cmd$));
  return Rx.Observable.create<string[]>(o => {
    notice$.filter(n => n.routeId === namesInScopeRoute)
      .subscribe(n => {
        o.onNext(n.feedbackContent.message.split("\n"))
      });
  });
}
