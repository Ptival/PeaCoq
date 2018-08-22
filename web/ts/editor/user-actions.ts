import * as FontSize from './font-size'
import { pickFile, saveFile, setupLoadFile, setupSaveFile } from './toolbar'

interface UserActionStreams {
  goTo$ : Rx.Observable<{}>,
  loadedFile$ : Rx.Observable<{}>,
  next$ : Rx.Observable<{}>,
  prev$ : Rx.Observable<{}>,
}

export function setup(
  doc : ICoqDocument,
  toolbarStreams : ToolbarStreams,
  shortcutsStreams : ShortcutsStreams
) : UserActionStreams {
  const fontDecreasedStream =
    Rx.Observable
      .merge(toolbarStreams.fontDecrease, shortcutsStreams.fontDecrease)
      .do(FontSize.decrement)
      .share()
  const fontIncreasedStream =
    Rx.Observable
      .merge(toolbarStreams.fontIncrease, shortcutsStreams.fontIncrease)
      .do(FontSize.increment)
      .share()
  Rx.Observable
    .merge(fontIncreasedStream, fontDecreasedStream)
    .subscribe(() => { FontSize.update(doc) })
  const goTo$ = Rx.Observable
    .merge(toolbarStreams.goToCaret, shortcutsStreams.goToCaret)
  const next$ = Rx.Observable
    .merge(toolbarStreams.next, shortcutsStreams.next)
  const prev$ = Rx.Observable
    .merge(toolbarStreams.previous, shortcutsStreams.previous)
  Rx.Observable
    .merge(toolbarStreams.load, shortcutsStreams.load)
    .subscribe(pickFile)
  Rx.Observable
    .merge(toolbarStreams.save, shortcutsStreams.save)
    .subscribe(({}) => saveFile(doc))
  const loadedFilesStream = setupLoadFile(doc)
  setupSaveFile()
  return {
    goTo$ : goTo$,
    loadedFile$ : loadedFilesStream,
    next$ : next$,
    prev$ : prev$,
  }
}
