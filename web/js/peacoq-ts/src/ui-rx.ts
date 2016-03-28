function setupLoadFile(): Rx.Observable<string> {

  let id = "filepicker";

  let input = $("<input>", {
    "id": id,
    "type": "file",
    "style": "display: none;",
  }).appendTo($("body"));

  let filesToBeLoadedStream: Rx.Observable<File> =
    Rx.Observable
      .fromEvent(input, "change")
      .map((event) => {
        return (<HTMLInputElement>input.get(0)).files[0];
      })
    ;

  let loadedFilesStream: Rx.Observable<string> =
    filesToBeLoadedStream
      .flatMap((file) => {
        let reader = new FileReader();
        let promise: Promise<string> = new Promise((onResolve) => {
          reader.onload = () => { onResolve(reader.result); };
        });
        reader.readAsText(file);
        return Rx.Observable.fromPromise(promise);
      })
    ;

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
