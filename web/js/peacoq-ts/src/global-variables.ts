export let coqDocument: ICoqDocument;

export let proofTrees: IProofTree[] = [];

// TODO: make this a record
export let pretty: ITab;
export let foreground: IEditorTab;
export let background: IEditorTab;
export let shelved: IEditorTab;
export let givenUp: IEditorTab;

export let notices: IEditorTab
export let warnings: IEditorTab;
export let errors: IEditorTab;
export let infos: IEditorTab;
export let debug: IEditorTab;
export let failures: IEditorTab;
export let feedback: IEditorTab;
export let jobs: IEditorTab;

export let allEditorTabs: IEditorTab[] = [];

export function setCoqDocument(d: ICoqDocument) {
  coqDocument = d;
}

export function setTabs(
  tpretty: ITab, tforeground: IEditorTab, tbackground: IEditorTab,
  tshelved: IEditorTab, tgivenUp: IEditorTab, tnotices: IEditorTab,
  twarnings: IEditorTab, terrors: IEditorTab, tinfos: IEditorTab,
  tdebug: IEditorTab, tfailures: IEditorTab, tfeedback: IEditorTab,
  tjobs: IEditorTab
) {
  pretty = tpretty;
  foreground = tforeground;
  background = tbackground;
  shelved = tshelved;
  givenUp = tgivenUp;
  notices = tnotices;
  warnings = twarnings;
  errors = terrors;
  infos = tinfos;
  debug = tdebug;
  failures = tfailures;
  feedback = tfeedback;
  jobs = tjobs;
}
