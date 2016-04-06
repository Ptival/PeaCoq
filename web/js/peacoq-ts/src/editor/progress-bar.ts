import * as Edit from "./edit";
import * as EditStage from "./edit-stage";
import * as Global from "../global-variables";
import * as Theme from "../theme";

let barItemClass = "progress-bar-item";
let progressBarId = "progress-bar";

export function setupProgressBar(): void {
  Edit.editStageChange$.subscribe(updateProgressBar);
  let barClick$: Rx.Observable<Event> =
    Rx.Observable.fromEvent<Event>(document, "click")
      .filter(e => $(e.target).hasClass(barItemClass));
  let barMouseOver$: Rx.Observable<Event> =
    Rx.Observable.fromEvent<Event>(document, "mouseover")
      .filter(e => $(e.target).hasClass(barItemClass));
  let barMouseOut$: Rx.Observable<Event> =
    Rx.Observable.fromEvent<Event>(document, "mouseout")
      .filter(e => $(e.target).hasClass(barItemClass));
  barMouseOver$.subscribe(
    e => $(e.target).css("border", `4px solid ${Theme.theme.highlight}`)
  );
  barMouseOut$.subscribe(e => $(e.target).css("border", "none"));
  barMouseOver$.subscribe(e => {
    let targetEdit: IEdit = d3.select(e.target).data()[0];
    targetEdit.stage.highlight();
  });
  barMouseOut$.subscribe(e => {
    let targetEdit: IEdit = d3.select(e.target).data()[0];
    targetEdit.stage.unhighlight();
  });
  barClick$.subscribe(e => {
    let targetEdit: IEdit = d3.select(e.target).data()[0];
    Global.coqDocument.moveCursorToPositionAndCenter(targetEdit.getStopPosition());
    Global.coqDocument.editor.focus();
  });
}

function updateProgressBar(): void {
  let allEdits: IEdit[] = Global.coqDocument.getAllEdits();
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
    .style("background-color", (d: IEdit) => {
      let color = "black";
      d.stage instanceof EditStage.ToProcess && (color = Theme.theme.toprocess);
      d.stage instanceof EditStage.BeingProcessed && (color = Theme.theme.processing);
      d.stage instanceof EditStage.Ready && (color = Theme.theme.processed);
      return color;
    })
    ;
  selection.exit().remove();
}
