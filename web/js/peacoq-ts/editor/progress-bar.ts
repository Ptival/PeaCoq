import * as DebugFlags from "../debug-flags";
import * as Edit from "./edit";
import * as Global from "../global-variables";
import * as Theme from "../theme";

let barItemClass = "progress-bar-item";
let progressBarId = "progress-bar";

export function setupProgressBar(): void {
  Rx.Observable.merge(
    Theme.afterChange$,
    Global.coqDocument.edits.editCreated$,
    Global.coqDocument.edits.editChangedStage$,
    Global.coqDocument.edits.editRemoved$
  ).subscribe(updateProgressBar);
  let barClick$: Rx.Observable<Event> =
    Rx.Observable.fromEvent<Event>(document, "click")
      .filter(e => $(e.target).hasClass(barItemClass));
  if (DebugFlags.progressBarClick) { subscribeAndLog(barClick$); }
  let barMouseOver$: Rx.Observable<Event> =
    Rx.Observable.fromEvent<Event>(document, "mouseover")
      .filter(e => $(e.target).hasClass(barItemClass));
  let barMouseOut$: Rx.Observable<Event> =
    Rx.Observable.fromEvent<Event>(document, "mouseout")
      .filter(e => $(e.target).hasClass(barItemClass));
  barMouseOver$.subscribe(
    e => $(e.target).css("background-color", `${Theme.theme.highlight}`)
  );
  barMouseOut$.subscribe(e => {
    let targetEdit: IEdit<any> = d3.select(e.target).data()[0];
    $(e.target).css("background-color", `${targetEdit.getColor()}`);
  });
  barMouseOver$.subscribe(e => {
    let targetEdit: IEdit<any> = d3.select(e.target).data()[0];
    targetEdit.highlight();
  });
  barMouseOut$.subscribe(e => {
    let targetEdit: IEdit<any> = d3.select(e.target).data()[0];
    targetEdit.unhighlight();
  });
  barClick$.subscribe(e => {
    let targetEdit: IEdit<any> = d3.select(e.target).data()[0];
    Global.coqDocument.moveCursorToPositionAndCenter(targetEdit.stopPosition);
    Global.coqDocument.editor.focus();
  });
}

function updateProgressBar(): void {
  let allEdits = Global.coqDocument.getAllEdits();
  let selection =
    d3.select(`#${progressBarId}`)
      .selectAll("div")
      .data(allEdits, e => `${e.id}`);
  // for now we can append, eventually we might need sorting
  selection.enter().append("div")
    .classed(barItemClass, true)
    .style("height", "100%")
    .style("display", "inline-block")
    ;
  let eltWidth = $(`#${progressBarId}`).width() / allEdits.length;
  selection
    .style("width", `${eltWidth}px`)
    .style("background-color", (d: IEdit<any>) => d.getColor())
    .attr("title", d => "StateID: " + d.getStateId().caseOf({
      nothing: () => "unassigned yet",
      just: sid => `${sid}`,
    }))
    ;
  selection.exit().remove();
}
