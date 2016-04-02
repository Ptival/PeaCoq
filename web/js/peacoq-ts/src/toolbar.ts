import { coqDocument } from "./coq85";
import { switchToBright, switchToDark } from "./theme";

let filePickerId = "filepicker";

interface ToolbarStreams {
  fontDecrease: Rx.Observable<{}>;
  fontIncrease: Rx.Observable<{}>;
  goToCaret: Rx.Observable<{}>;
  load: Rx.Observable<{}>;
  next: Rx.Observable<{}>;
  previous: Rx.Observable<{}>;
  save: Rx.Observable<{}>;
}

export function setupToolbar(): ToolbarStreams {

  let toolbar = $("#toolbar").w2toolbar({ name: "w2toolbar" });
  let loadClickStream = addButton(toolbar, { caption: "Load", icon: "floppy-open" });
  let saveClickStream = addButton(toolbar, { caption: "Save", icon: "floppy-save" });
  toolbar.add({ type: "break", id: "toolbar-break-0" });
  let previousClickStream = addButton(toolbar, { caption: "Previous", icon: "arrow-up" });
  let goToCaretClickStream = addButton(toolbar, { caption: "To Caret", icon: "arrow-right" });
  let nextClickStream = addButton(toolbar, { caption: "Next", icon: "arrow-down" });
  toolbar.add([
    { type: "break", id: "toolbar-break-1" },
  ]);
  let fontDecreaseClickStream = addButton(toolbar, { id: "font-decrease", icon: "minus" });
  toolbar.add([
    { type: "button", id: "toolbar-font", img: "glyphicon glyphicon-text-height", disabled: true },
  ]);
  let fontIncreaseClickStream = addButton(toolbar, { id: "font-increase", icon: "plus" });
  toolbar.add([
    { type: "spacer", id: "toolbar-spacer" },
    { type: "radio", id: "toolbar-bright", group: "1", caption: "Bright", checked: true, onClick: switchToBright },
    { type: "radio", id: "toolbar-dark", group: "1", caption: "Dark", onClick: switchToDark },
  ]);

  return {
    fontDecrease: fontDecreaseClickStream,
    fontIncrease: fontIncreaseClickStream,
    goToCaret: goToCaretClickStream,
    load: loadClickStream,
    next: nextClickStream,
    previous: previousClickStream,
    save: saveClickStream,
  };

}

export function setupLoadFile(): Rx.Observable<string> {

  let input = $("<input>", {
    "id": filePickerId,
    "type": "file",
    "style": "display: none;",
  }).appendTo($("body"));

  let inputChangeStream: Rx.Observable<File> =
    Rx.Observable
      .fromEvent<Event>(input, "change")
      .map((event) => {
        let file = (<HTMLInputElement>input.get(0)).files[0];
        // necessary for change to fire upon reopening same file
        $(event.target).val("");
        return file;
      })
      .share()
    ;

  let loadedFilesStream: Rx.Observable<string> =
    inputChangeStream
      .flatMap((file) => {
        let reader = new FileReader();
        let promise: Promise<string> = new Promise((onResolve) => {
          reader.onload = () => { onResolve(reader.result); };
        });
        reader.readAsText(file);
        return Rx.Observable.fromPromise(promise);
      })
      .share()
    ;

  // TODO: This belongs somewhere else (document-related)
  loadedFilesStream.subscribe((text) => {
    coqDocument.removeAllEdits();
    coqDocument.resetEditor(text);
  });

  return loadedFilesStream;

}

export function setupSaveFile() {
  $("<a>", {
    "download": "output.v",
    "id": "save-local-link",
  })
    .css("display", "none")
    .appendTo($("body"))
    ;
}

interface ButtonSpecification {
  caption?: string;
  id?: string;
  icon: string;
}

function addButton(
  toolbar: W2UI.W2Toolbar,
  spec: ButtonSpecification
): Rx.Observable<{}> {
  if (!(spec.hasOwnProperty || spec.id)) { throw "addButton: needs a caption or an id"; }
  let id = "button-" + (spec.id ? spec.id : spec.caption);
  // add the button regardless of subscriptions
  let button = toolbar.add({
    type: "button",
    id: id,
    caption: spec.caption ? spec.caption : "",
    img: "glyphicon glyphicon-" + spec.icon,
  });
  return Rx.Observable.create((observer) => {
    toolbar.get(id)["onClick"] = () => observer.onNext({});
  }).share();
}

export function pickFile(): void {
  $("#" + filePickerId).click();
}

export function saveFile(): void {
  let editor = coqDocument.editor;
  let text = editor.getValue();
  let blob = new Blob([text], { type: 'text/plain;charset=UTF-8' });
  let url = window.URL.createObjectURL(blob);
  $("#save-local-link").attr("href", url);
  $("#save-local-link")[0].click();
  // TODO: this should be done elsewhere
  editor.focus();
}
