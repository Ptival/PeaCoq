import * as MyRx from "./rx";

export let coqDocument: ICoqDocument;

export let proofTrees: IProofTree[] = [];

export let tabs: ITabs;

export function getAllEditorTabs(): IEditorTab[] {
  return [
    tabs.foreground,
    tabs.background,
    tabs.shelved,
    tabs.givenUp,
    tabs.notices,
    tabs.warnings,
    tabs.errors,
    tabs.infos,
    tabs.debug,
    tabs.failures,
    // tabs.feedback,
    tabs.jobs,
  ]
}

export function setCoqDocument(d: ICoqDocument) {
  coqDocument = d;
}

export function setTabs(t: ITabs) {
  tabs = t;
}
