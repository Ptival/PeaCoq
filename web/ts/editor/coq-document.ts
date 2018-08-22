import * as _ from 'lodash'

import { Anchor } from './anchor'
import * as Stage from './stage'
import { SentenceArray } from './sentence-array'
import { errorUnderlineClass, theme } from '../peacoq/theme'
import { ProofTreeStack } from '../prooftree/stack'
import * as Command from '../sertop/command'
import * as ControlCommand from '../sertop/control-command'
import { setup as setupSertop } from '../sertop/sertop'

function tipKey(t : Tip) : number {
  return t.caseOf({
    nothing : () => -1,
    just : s => s.sentenceId,
  })
}

export class CoqDocument implements ICoqDocument {
  public addsToProcess$ : Rx.Observable<StmAdd$>
  private beginAnchor : Anchor
  private commandObserver : Rx.Observer<Command$>
  public command$ : Rx.Observable<Command$>
  public contextPanel : IContextPanel
  public editorChange$ : Rx.Observable<AceAjax.EditorChangeEvent>
  public sentences : ISentenceArray
  private endAnchor : Anchor
  public input$ : Command$
  private nextObserver : Rx.Observer<{}>
  public output$s : CoqtopOutputStreams
  public proofTrees : ProofTreeStack
  public sentencesChanged$ : Rx.Observable<{}>
  public sentenceBeingProcessed$ : Rx.Observable<ISentence<IBeingProcessed>>
  public sentenceProcessed$ : Rx.Observable<ISentence<IProcessed>>
  public session : AceAjax.IEditSession
  private tipSubject : Rx.Subject<Tip>
  public debouncedTip$ : Rx.Observable<Tip>
  public tip$ : Rx.Observable<Tip>

  constructor(
    public editor : AceAjax.Editor
  ) {
    const self = this
    this.sentences = new SentenceArray(this)
    // WARNING : This line must stay over calls to mkAnchor
    this.session = editor.getSession()
    this.beginAnchor = new Anchor(this, 0, 0, 'begin-marker', true)
    this.endAnchor = new Anchor(this, 0, 0, 'end-marker', false)
    this.editorChange$ =
      Rx.Observable
        .create<AceAjax.EditorChangeEvent>(observer => {
          self.session.on('change', (e) => observer.onNext(e))
        })
        .share()
    this.sentencesChanged$ = Rx.Observable.merge(
      this.sentences.sentenceCreated$,
      this.sentences.sentenceChangedStage$,
      this.sentences.sentenceRemoved$
    )
    // this.editsChange$ = this.editsChangeSubject.asObservable()
    const newEditSubject = new Rx.Subject<ISentence<IToProcess>>()
    this.proofTrees = new ProofTreeStack()
    this.sentenceBeingProcessed$ = this.sentences.sentenceBeingProcessed$
    this.sentenceProcessed$ = this.sentences.sentenceProcessed$
    this.tipSubject = new Rx.Subject<Tip>()
    // Use distinctUntilChanged because PeaCoq automation triggers spurious
    // tipSubject notifications for the same tip
    // We don't want tip$ to be ref-counted as it creates problems with automation
    const tip$ = this.tipSubject.distinctUntilChanged(tipKey).publish()
    this.tip$ = tip$
    // this.tip$.subscribe(t => console.log('tip$ from coq-document', t.sentenceId))
    this.debouncedTip$ = this.tipSubject.distinctUntilChanged(tipKey).debounce(250).share()
    this.sentenceBeingProcessed$.subscribe(s => this.setTip(just(s)))

    const nextSubject = new Rx.ReplaySubject(1)
    this.nextObserver = nextSubject.asObserver()
    const sentencesToProcess$ = this.nextSentence(nextSubject.asObservable())

    const commandSubject = new Rx.Subject<Command$>()

    this.input$ =
      commandSubject
        // merge sequence of groups of commands into one sequence of commands
        .concatMap(cmd$ => cmd$
        // .do(e => console.log('ELEMENT IN', e))
        // .doOnCompleted(() => console.log('COMPLETED'))
        )
        // .do(cmd => console.log('ELEMENT OUT', cmd))
    this.output$s = setupSertop(this.input$)

    this.commandObserver = commandSubject.asObserver()
    const command$ = commandSubject.asObservable().publish()
    this.command$ = command$

    sentencesToProcess$.subscribe(e => this.moveCursorToPositionAndCenter(e.stopPosition))
    sentencesToProcess$
      .map(s => {
        const command = new Command.Control(new ControlCommand.StmAdd({}, s.query, false))
        s.commandTag = just(command.tag)
        return Rx.Observable.just(command)
      })
      .subscribe(cmd$ => this.sendCommands(cmd$))

    tip$.connect()
    command$.connect()
  }

  public getActiveProofTree() : Maybe<IProofTree> {
    return (
      this.proofTrees.length > 0
        ? just(this.proofTrees.peek())
         : nothing<IProofTree>()
    )
  }

  public getAllSentences() : ISentence<IStage>[] { return this.sentences.getAll() }

  public getSentenceAtPosition(pos : AceAjax.Position) : Maybe<ISentence<IStage>> {
    const edit = _(this.getAllSentences()).find(e => e.containsPosition(pos))
    return edit ? just(edit)  : nothing<ISentence<IStage>>()
  }

  public getSentenceByStateId(id : StateId) : Maybe<ISentence<IStage>> {
    const edit = _(this.getAllSentences()).find(e => e.getStateId().caseOf({
      nothing : () => false,
      just : s => s === id,
    }))
    return edit ? just(edit)  : nothing<ISentence<IStage>>()
  }

  public getSentenceByTag(tag : CommandTag) : Maybe<ISentence<IStage>> {
    const edit = _(this.getAllSentences()).find(e => e.commandTag.caseOf({
      nothing : () => false,
      just : s => s === tag,
    }))
    return edit ? just(edit)  : nothing<ISentence<IStage>>()
  }

  public getSentencesBeingProcessed() : ISentence<IBeingProcessed>[] {
    return <any>this.getAllSentences().filter(e => e.stage instanceof Stage.BeingProcessed)
  }

  public getSentencesToProcess() : ISentence<IToProcess>[] {
    return <any>this.getAllSentences().filter(e => e.stage instanceof Stage.ToProcess)
  }

  public getProcessedSentences() : ISentence<IProcessed>[] {
    return <any>this.getAllSentences().filter(e => e.stage instanceof Stage.Processed)
  }

  // getStopPositions() : AceAjax.Position[] {
  //   return _(this.editsProcessed).map(function(e) { return e.getStopPosition() }).value()
  // }

  // getLastSentence() : Maybe<ISentence<IEditStage>> {
  //   return this.edits.getLast()
  // }

  public getLastSentenceStop() : AceAjax.Position {
    return this.sentences.getLast().caseOf({
      nothing : () => this.beginAnchor.anchor.getPosition(),
      just : last => last.stopPosition,
    })
  }

  public moveCursorToPositionAndCenter(pos : AceAjax.Position) : void {
    // this prevents the editor from marking selected the region jumped
    this.editor.session.selection.clearSelection()
    this.editor.moveCursorToPosition(pos)
    this.editor.scrollToLine(pos.row, true, true, () => { })
  }

  public movePositionRight(pos : AceAjax.Position, n : number) : AceAjax.Position {
    if (n === 0) { return pos }
    const row = pos.row
    const column = pos.column
    const line = this.session.getLine(row)
    if (column < line.length) {
      return this.movePositionRight({
        'row' : row,
        'column' : column + 1
      }, n - 1)
    } else if (row < this.session.getLength()) {
      return this.movePositionRight({
        'row' : row + 1,
        'column' : 0
      }, n - 1)
    } else {
      return pos
    }
  }

  // onProcessEditsFailure(vf : ValueFail) : Promise<any> {
  //   if (!(vf instanceof ValueFail)) {
  //     throw vf
  //   }
  //   this.editBeingProcessed.fmap((e) => e.onRemove())
  //   this.editBeingProcessed = nothing()
  //   _(this.editsToProcess).each((e) => e.onRemove())
  //   this.editsToProcess = []
  //   reportFailure(vf.message)
  //   console.log(vf.stateId)
  //   if (vf.stateId !== 0) {
  //     // TODO : also need to cancel edits > vf.stateId
  //     return peaCoqEditAt(vf.stateId)
  //   } else {
  //     return Promise.reject(vf)
  //   }
  // }

  // processEdits() : Promise<any> {
  //   const self = this
  //   if (this.editsToProcess.length === 0 || isJust(this.editBeingProcessed)) {
  //     return Promise.resolve()
  //   }
  //   const ebp = new EditBeingProcessed(this.editsToProcess.shift())
  //   this.editBeingProcessed = just(ebp)
  //   return (
  //     peaCoqAddPrime(ebp.query)
  //       .then((response) => {
  //         const stopPos = ebp.getStopPosition()
  //         self.session.selection.clearSelection()
  //         self.editor.moveCursorToPosition(stopPos)
  //         self.editor.scrollToLine(stopPos.row, true, true, () => { })
  //         self.editor.focus()
  //         const sid : number = response.stateId
  //         const ls = lastStatus
  //         const s = peaCoqStatus(false)
  //         const g = s.then(peaCoqGoal)
  //         const c = g.then(peaCoqGetContext)
  //         return Promise.all<any>([s, g, c]).then(
  //           ([s, g, c] : [Status, Goals, PeaCoqContext]) => {
  //             const e = new ProcessedEdit(ebp, sid, s, g, c)
  //             self.editsProcessed.push(e)
  //             _(editHandlers).each((h) => h(ebp.query, sid, ls, s, g, c))
  //             this.editBeingProcessed = nothing()
  //             return self.processEdits()
  //           })
  //       })
  //       .catch(self.onProcessEditsFailure.bind(self))
  //   )
  // }

  public markError(
    range : AceAjax.Range,
    clear$ : Rx.Observable<{}>
  ) : void {
    const markerId = this.session.addMarker(range, errorUnderlineClass, 'text', false)
    this.moveCursorToPositionAndCenter(range.start)
    const markerChanged$ = this.editorChange$
      .filter(e => range.contains(e.start.row, e.start.column) || range.contains(e.end.row, e.end.column))
      .take(1)
    Rx.Observable.merge(
      markerChanged$,
      clear$
    ).subscribe(() => this.session.removeMarker(markerId))
  }

  public next() : void {
    this.nextObserver.onNext({})
  }

  public nextSentence(next$ : Rx.Observable<{}>) : Rx.Observable<ISentence<IToProcess>> {
    return next$
      .concatMap<ISentence<IToProcess>>(() => {
        const lastEditStopPos = this.getLastSentenceStop()
        const endPos = this.endAnchor.anchor.getPosition()
        const unprocessedRange =
          new AceAjax.Range(
            lastEditStopPos.row, lastEditStopPos.column,
            endPos.row, endPos.column
          )
        const unprocessedText = this.session.getTextRange(unprocessedRange)
        if (CoqStringUtils.coqTrimLeft(unprocessedText) === '') {
          return []
        }
        const nextIndex = CoqStringUtils.next(unprocessedText)
        const newStopPos = this.movePositionRight(lastEditStopPos, nextIndex)
        const query = unprocessedText.substring(0, nextIndex)
        const previousEdit = this.sentences.getLast()
        const stage = new Stage.ToProcess(this, lastEditStopPos, newStopPos)
        const edit : ISentence<IToProcess> =
          this.sentences.createSentence(this, lastEditStopPos, newStopPos, query, previousEdit, stage)
        // debugger
        return [edit]
      })
      .share()

  }

  public recenterEditor() {
    const pos = this.editor.getCursorPosition()
    this.editor.scrollToLine(pos.row, true, true, () => { })
  }

  public resetEditor(text : string) {
    this.session.setValue(text)
    this.editor.focus()
    this.editor.scrollToLine(0, true, true, () => { })
  }

  public removeAllSentences() : void { this.sentences.removeAll() }

  public removeSentence(e : ISentence<any>) : void { this.sentences.remove(e) }

  // removeEditAndFollowingOnes(e : ISentence<any>) : void {
  //   this.edits.removeEditAndFollowingOnes(e)
  // }

  public removeSentences(pred : (e : ISentence<any>) => boolean) : void {
    this.sentences.removeSentences(pred)
  }

  // removeFollowingEdits(e : ISentence<any>) : void {
  //   this.edits.removeFollowingEdits(e)
  // }

  public removeSentencesByStateIds(ids : StateId[]) : void {
    this.sentences.removeSentences(e => e.getStateId().caseOf({
      nothing : () => false,
      just : id => _(ids).includes(id),
    }))
  }

  // removeEdits(
  //   predicate : (e : ProcessedEdit) => boolean,
  //   beforeRemoval? : (e : ProcessedEdit) => void
  // ) {
  //   _.remove(this.editsProcessed, function(e) {
  //     const toBeRemoved = predicate(e)
  //     if (toBeRemoved) {
  //       if (beforeRemoval) { beforeRemoval(e) }
  //       e.onRemove()
  //     }
  //     return toBeRemoved
  //   })
  // }

  public sendCommands(s : Command$) : void {
    this.commandObserver.onNext(s)
  }

  public setTip(tip : Tip) : void {
    this.tipSubject.onNext(tip)
  }

}
