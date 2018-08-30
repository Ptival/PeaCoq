import * as Loc from '../coq/lib/loc'

export function coqLocationFromSexp(o : any) : Loc.t {
    const [[, fName], [, lineNb], [, bolPos], [, lineNbLast], [, bolPosLast], [, bp], [, ep]] = o
    return new Loc.t(
        fName,
        lineNb,
        bolPos,
        lineNbLast,
        bolPosLast,
        bp,
        ep,
    )
}

export function escapeQuotes(s : string) : string {
    return (
        s
            .replace(/'/g, `\\'`)
            .replace(/"/g, `\\"`)
    )
}
