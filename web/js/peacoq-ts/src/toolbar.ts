
interface ToolbarStreams {
  goToCaretClick: Rx.Observable<{}>;
  loadClick: Rx.Observable<{}>;
  nextClick: Rx.Observable<{}>;
  previousClick: Rx.Observable<{}>;
}

function setupToolbar(): ToolbarStreams {

  let toolbar = $("#toolbar").w2toolbar({ name: "w2toolbar" });
  let loadClickStream = addButton(toolbar, "Load", "floppy-open");
  let saveClickStream = addButton(toolbar, "Save", "floppy-save");
  toolbar.add({ type: "break", id: "toolbar-break-0" });
  let previousClickStream = addButton(toolbar, "Previous", "arrow-up");
  let goToCaretClickStream = addButton(toolbar, "To Caret", "arrow-right");
  let nextClickStream = addButton(toolbar, "Next", "arrow-down");
  toolbar.add([
    { type: "break", id: "toolbar-break-1" },
    { type: "button", id: "toolbar-font-decrease", img: "glyphicon glyphicon-minus", onClick: () => fontDecrease(coqDocument) },
    { type: "button", id: "toolbar-font", img: "glyphicon glyphicon-text-height", disabled: true },
    { type: "button", id: "toolbar-font-increase", img: "glyphicon glyphicon-plus", onClick: () => fontIncrease(coqDocument) },
    { type: "spacer", id: "toolbar-spacer" },
    { type: "radio", id: "toolbar-bright", group: "1", caption: "Bright", checked: true, onClick: Theme.switchToBright },
    { type: "radio", id: "toolbar-dark", group: "1", caption: "Dark", onClick: Theme.switchToDark },
  ]);

  return {
    goToCaretClick: goToCaretClickStream,
    loadClick: loadClickStream,
    nextClick: nextClickStream,
    previousClick: previousClickStream,
  };

}

function setupLoadFile(): Rx.Observable<string> {

  let id = "filepicker";

  let input = $("<input>", {
    "id": id,
    "type": "file",
    "style": "display: none;",
  }).appendTo($("body"));

  let inputChangeStream: Rx.ConnectableObservable<File> =
    Rx.Observable
      .fromEvent<Event>(input, "change")
      .map((event) => {
        let file = (<HTMLInputElement>input.get(0)).files[0];
        // necessary for change to fire upon reopening same file
        $(event.target).val("");
        return file;
      })
      .publish()
    ;
  inputChangeStream.connect();

  let loadedFilesStream: Rx.ConnectableObservable<string> =
    inputChangeStream
      .flatMap((file) => {
        let reader = new FileReader();
        let promise: Promise<string> = new Promise((onResolve) => {
          reader.onload = () => { onResolve(reader.result); };
        });
        reader.readAsText(file);
        return Rx.Observable.fromPromise(promise);
      })
      .publish()
    ;
  loadedFilesStream.connect();

  // TODO: This belongs somewhere else (document-related)
  loadedFilesStream.subscribe((text) => {
    coqDocument.removeEdits(() => true);
    coqDocument.resetEditor(text);
  });

  return loadedFilesStream;

}

function addButton(
  toolbar: W2UI.W2Toolbar,
  caption: string,
  glyphicon: string
): Rx.Observable<{}> {
  let clickStream = Rx.Observable.create((observer) => {
    toolbar.add({
      type: "button",
      id: "button-" + caption,
      caption: caption,
      img: "glyphicon glyphicon-" + glyphicon,
      onClick: () => observer.onNext({}),
    });
  }).publish();
  clickStream.connect();
  return clickStream;
}
