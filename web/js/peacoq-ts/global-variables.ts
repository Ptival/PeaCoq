import * as MyRx from "./rx";

export let coqDocument: ICoqDocument;

export let proofTrees: IProofTree[] = [];

export function setCoqDocument(d: ICoqDocument) {
  coqDocument = d;
}
