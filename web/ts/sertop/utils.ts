
export function coqLocationFromSexp(o : any) : CoqLocation {
  const [[, fName], [, lineNb], [, bolPos], [, lineNbLast], [, bolPosLast], [, bp], [, ep]] = o
  return {
    fName,
    lineNb,
    bolPos,
    lineNbLast,
    bolPosLast,
    bp,
    ep,
  }
}
