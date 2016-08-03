import { theme } from "../theme";

const CoqMode = ace.require("peacoq-js/mode-coq").Mode;

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

export function setupMainEditor(
  doc: ICoqDocument,
  e: AceAjax.Editor
) {
  setupEditor(e);
  // used to set completion here, but would rather make that a separate concern
}
