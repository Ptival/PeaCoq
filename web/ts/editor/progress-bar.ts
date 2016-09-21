import * as DebugFlags from "../peacoq/debug-flags"
import * as Theme from "../peacoq/theme"
import { debounceAndThrottle } from "../rxjs/operators"

let barItemClass = "progress-bar-item"
let progressBarId = "progress-bar"

export function setupProgressBar(doc: ICoqDocument): void {
  // TODO: progress bar should update when command ID is assigned
  Rx.Observable.merge(
    Theme.afterChange$,
    doc.sentencesChanged$
  )
    // Next line should probably be .audit(250) in RxJS 5
    // it makes sure we get running every 250ms and at least once after
    // 250ms of silence following an emission
    .let(debounceAndThrottle(250))
    .subscribe(() => updateProgressBar(doc))
  let barClick$: Rx.Observable<Event> =
    Rx.Observable.fromEvent<Event>(document, "click")
      .filter(e => $(e.target).hasClass(barItemClass))
  if (DebugFlags.progressBarClick) { barClick$.subscribe(c => console.log(c)) }
  let barMouseOver$: Rx.Observable<Event> =
    Rx.Observable.fromEvent<Event>(document, "mouseover")
      .filter(e => $(e.target).hasClass(barItemClass))
  let barMouseOut$: Rx.Observable<Event> =
    Rx.Observable.fromEvent<Event>(document, "mouseout")
      .filter(e => $(e.target).hasClass(barItemClass))
  barMouseOver$.subscribe(
    e => $(e.target).css("background-color", `${Theme.theme.highlight}`)
  )
  barMouseOut$.subscribe(e => {
    let targetEdit: ISentence<any> = d3.select(e.target).data()[0]
    $(e.target).css("background-color", `${targetEdit.getColor()}`)
  })
  barMouseOver$.subscribe(e => {
    let targetEdit: ISentence<any> = d3.select(e.target).data()[0]
    targetEdit.highlight()
  })
  barMouseOut$.subscribe(e => {
    let targetEdit: ISentence<any> = d3.select(e.target).data()[0]
    targetEdit.unhighlight()
  })
  barClick$.subscribe(e => {
    let targetEdit: ISentence<any> = d3.select(e.target).data()[0]
    doc.moveCursorToPositionAndCenter(targetEdit.stopPosition)
    doc.editor.focus()
  })
}

function updateProgressBar(doc: ICoqDocument): void {
  let allEdits = doc.getAllSentences()
  let selection =
    d3.select(`#${progressBarId}`)
      .selectAll("div")
      .data(allEdits, e => `${e.sentenceId}`)
  // for now we can append, eventually we might need sorting
  selection.enter().append("div")
    .classed(barItemClass, true)
    .style("height", "100%")
    .style("display", "inline-block")

  let eltWidth = $(`#${progressBarId}`).width() / allEdits.length
  selection
    .style("width", `${eltWidth}px`)
    .style("background-color", (d: ISentence<any>) => d.getColor())
    .attr("title", d => {
      const commandId = d.commandTag.caseOf({
        nothing: () => "unassigned yet",
        just: cid => `${cid}`,
      })
      const stateId = d.getStateId().caseOf({
        nothing: () => "unassigned yet",
        just: sid => `${sid}`,
      })
      return `Sentence ID: ${d.sentenceId}, Command ID: ${commandId}, State ID: ${stateId}`
    })

  selection.exit().remove()
}
