// TODO : this import seems weird
import { onResize } from '../peacoq/on-resize'
import { switchToBright, switchToDark } from '../peacoq/theme'

const filePickerId = 'filepicker'

export function setup(doc : ICoqDocument) : ToolbarStreams {

  const toolbar = $('#toolbar').w2toolbar({ name : 'w2toolbar' })
  const loadClickStream = addButton(toolbar, { caption : 'Load', icon : 'floppy-open' })
  const saveClickStream = addButton(toolbar, { caption : 'Save', icon : 'floppy-save' })
  toolbar.add({ type : 'break', id : 'toolbar-break-0' })
  const previousClickStream = addButton(toolbar, { caption : 'Previous', icon : 'arrow-up' })
  const goToCaretClickStream = addButton(toolbar, { caption : 'To Caret', icon : 'arrow-right' })
  const nextClickStream = addButton(toolbar, { caption : 'Next', icon : 'arrow-down' })
  toolbar.add([
    { type : 'break', id : 'toolbar-break-1' },
  ])
  const fontDecreaseClickStream = addButton(toolbar, { id : 'font-decrease', icon : 'minus' })
  toolbar.add([
    { type : 'button', id : 'toolbar-font', img : 'glyphicon glyphicon-text-height', disabled : true },
  ])
  const fontIncreaseClickStream = addButton(toolbar, { id : 'font-increase', icon : 'plus' })
  toolbar.add([
    { type : 'button', id : 'toolbar-resize', caption : 'Resize', onClick : () => onResize(doc) },
    { type : 'spacer', id : 'toolbar-spacer' },
    { type : 'radio', id : 'toolbar-bright', group : '1', caption : 'Bright', checked : true, onClick : () => switchToBright(doc) },
    { type : 'radio', id : 'toolbar-dark', group : '1', caption : 'Dark', onClick : () => switchToDark(doc) },
  ])

  return {
    fontDecrease : fontDecreaseClickStream,
    fontIncrease : fontIncreaseClickStream,
    goToCaret : goToCaretClickStream,
    load : loadClickStream,
    next : nextClickStream,
    previous : previousClickStream,
    save : saveClickStream,
  }

}

export function setupLoadFile(doc : ICoqDocument) : Rx.Observable<string> {

  const input = $('<input>', {
    'id' : filePickerId,
    'type' : 'file',
    'style' : 'display : none;',
  }).appendTo($('body'))

  const inputChangeStream : Rx.Observable<File> =
    Rx.Observable
      .fromEvent<Event>(input, 'change')
      .map((event) => {
        const elt = <HTMLInputElement>input.get(0)
        if (elt === null) {
          debugger
          throw input
        }
        const files = elt.files
        if (files === null || files.length === 0) {
          debugger
          throw input
        }
        const file = files[0]
        // necessary for change to fire upon reopening same file
        if (event.target) {
          $(event.target).val('')
        }
        return file
      })
      .share()

  const loadedFilesStream : Rx.Observable<string> =
    inputChangeStream
      .flatMap((file) => {
        const reader = new FileReader()
        const promise : Promise<string> = new Promise((onResolve, onReject) => {
          reader.onload = () => {
            if (typeof reader.result === 'string') {
              onResolve(reader.result)
            }
            else {
              onReject(reader.result)
            }
          }
        })
        reader.readAsText(file)
        return Rx.Observable.fromPromise(promise)
      })
      .share()

  // TODO : This belongs somewhere else (document-related)
  loadedFilesStream.subscribe((text) => {
    doc.removeAllSentences()
    doc.resetEditor(text)
  })

  return loadedFilesStream

}

export function setupSaveFile() {
  $('<a>', {
    'download' : 'output.v',
    'id' : 'save-local-link',
  })
    .css('display', 'none')
    .appendTo($('body'))

}

interface ButtonSpecification {
  caption? : string
  id? : string
  icon : string
}

function addButton(
  toolbar : W2UI.W2Toolbar,
  spec : ButtonSpecification
) : Rx.Observable<{}> {
  if (!(spec.hasOwnProperty || spec.id)) { throw 'addButton : needs a caption or an id' }
  const id = 'button-' + (spec.id ? spec.id : spec.caption)
  // add the button regardless of subscriptions
  const button = toolbar.add({
    type : 'button',
    id : id,
    caption : spec.caption ? spec.caption : '',
    img : 'glyphicon glyphicon-' + spec.icon,
  })
  return Rx.Observable.create((observer) => {
    toolbar.get(id)['onClick'] = () => observer.onNext({})
  }).share()
}

export function pickFile() : void {
  $('#' + filePickerId).click()
}

export function saveFile(doc : ICoqDocument) : void {
  const editor = doc.editor
  const text = editor.getValue()
  const blob = new Blob([text], { type : 'text/plain;charset=UTF-8' })
  const url = window.URL.createObjectURL(blob)
  $('#save-local-link').attr('href', url)
  $('#save-local-link')[0].click()
  // TODO : this should be done elsewhere
  editor.focus()
}
