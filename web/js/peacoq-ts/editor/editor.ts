import * as Completion from "./completion";
import * as Edit from "./edit";
import * as Global from "../global-variables";
import { theme } from "../theme";

const CoqMode = ace.require("peacoq-js/mode-coq").Mode;

class Editor implements IEditor {
  constructor(
    public document: ICoqDocument
  ) { }
}

export function setupEditor(e: AceAjax.Editor) {
  e.setTheme(theme.aceTheme);
  //const OCamlMode = ace.require("ace/mode/ocaml").Mode;
  //ace.require("ace/keyboard/textarea");
  e.session.setMode(new CoqMode());
  e.setOptions({
    enableBasicAutocompletion: true,
    enableLiveAutocompletion: false,
    enableSnippets: false,
    tabSize: 2,
  });
  e.setHighlightActiveLine(false);
  e.session.setUseSoftTabs(true);
  e.$blockScrolling = Infinity; // pestering warning
}

export function setupMainEditor(doc: ICoqDocument, e: AceAjax.Editor) {

  setupEditor(e);

  e.completers = [{ getCompletions: Completion.createGetCompletions(doc) }];

  // const addCompletion = (n: string) => {
  //   const row = e.completer ? e.completer.popup.getRow() : 0;
  //   names.push(n);
  //   e.execCommand("startAutocomplete");
  //   e.completer.popup.setRow(row);
  // };

}
