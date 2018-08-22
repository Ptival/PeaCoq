import * as d3Selection from 'd3-selection'
import * as DebugFlags from '../peacoq/debug-flags'
import * as Theme from '../peacoq/theme'
import { debounceAndThrottle } from '../rxjs/operators'

const barItemClass = 'progress-bar-item'
const progressBarId = 'progress-bar'

export function setupProgressBar(doc : ICoqDocument) : void {
  // TODO : progress bar should update when command ID is assigned
  Rx.Observable.merge(
    Theme.afterChange$,
    doc.sentencesChanged$
  )
    // Next line should probably be .audit(250) in RxJS 5
    // it makes sure we get running every 250ms and at least once after
    // 250ms of silence following an emission
    .let(debounceAndThrottle(250))
    .subscribe(() => updateProgressBar(doc))
  const barClick$ : Rx.Observable<Event> =
    Rx.Observable.fromEvent<Event>(document, 'click')
    .filter(e => e.target !== null && $(e.target).hasClass(barItemClass))
  if (DebugFlags.progressBarClick) { barClick$.subscribe(c => console.log(c)) }
  const barMouseOver$ : Rx.Observable<Event> =
    Rx.Observable.fromEvent<Event>(document, 'mouseover')
      .filter(e => e.target !== null && $(e.target).hasClass(barItemClass))
  const barMouseOut$ : Rx.Observable<Event> =
    Rx.Observable.fromEvent<Event>(document, 'mouseout')
      .filter(e => e.target !== null && $(e.target).hasClass(barItemClass))
  barMouseOver$.subscribe(
    e => e.target !== null && $(e.target).css('background-color', `${Theme.theme.highlight}`)
  )
  barMouseOut$.subscribe(e => {
    console.trace('FIXME', e)
    // const targetEdit : ISentence<any> = d3Selection.select(e.target).data()[0]
    // $(e.target).css('background-color', `${targetEdit.getColor()}`)
  })
  barMouseOver$.subscribe(e => {
    console.log('FIXME')
    // const targetEdit : ISentence<any> = d3Selection.select(e.target).data()[0]
    // targetEdit.highlight()
  })
  barMouseOut$.subscribe(e => {
    console.log('FIXME')
    // const targetEdit : ISentence<any> = d3Selection.select(e.target).data()[0]
    // targetEdit.unhighlight()
  })
  barClick$.subscribe(e => {
    console.log('FIXME')
    // const targetEdit : ISentence<any> = d3Selection.select(e.target).data()[0]
    // doc.moveCursorToPositionAndCenter(targetEdit.stopPosition)
    // doc.editor.focus()
  })
}

function updateProgressBar(doc : ICoqDocument) : void {
  const allEdits = doc.getAllSentences()

  const selection =
    d3Selection
      .select(`#${progressBarId}`)
      .selectAll<HTMLElement, ISentence<IStage>>('div')
      .data(allEdits, e => `${e.sentenceId}`)
  // for now we can append, eventually we might need sorting
  selection.enter().append('div')
    .classed(barItemClass, true)
    .style('height', '100%')
    .style('display', 'inline-block')

  const eltWidth = ($(`#${progressBarId}`).width() || 0) / allEdits.length
  selection
    .style('width', `${eltWidth}px`)
    .style('background-color', (d : ISentence<any>) => d.getColor())
    .attr('title', d => {
      const commandId = d.commandTag.caseOf({
        nothing : () => 'unassigned yet',
        just : cid => `${cid}`,
      })
      const stateId = d.getStateId().caseOf({
        nothing : () => 'unassigned yet',
        just : sid => `${sid}`,
      })
      return `Sentence ID: ${d.sentenceId}, Command ID: ${commandId}, State ID: ${stateId}`
    })

  selection.exit().remove()
}
