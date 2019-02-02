import * as _ from 'lodash'

export abstract class BlockType { }
export class PpHBox   extends BlockType { constructor(public x : number) { super() } }
export class PpVBox   extends BlockType { constructor(public x : number) { super() } }
export class PpHVBox  extends BlockType { constructor(public x : number) { super() } }
export class PpHoVBox extends BlockType { constructor(public x : number) { super() } }
export class PpTBox   extends BlockType {}

export type DocView
    = PpCmdEmpty
    | PpCmdString
    | PpCmdGlue
    | PpCmdBox
    | PpCmdTag
    | PpCmdPrintBreak
    | PpCmdForceNewline
    | PpCmdComment

export type T = DocView

export class PpCmdEmpty {
    private tag : 'PpCmdEmpty'
}

export class PpCmdString {
    constructor(
        public readonly str : string,
    ) { }
}

export class PpCmdGlue {
    constructor(
        public readonly docviews : DocView[],
    ) { }
}

export class PpCmdBox {
    constructor(
        public readonly blockType : BlockType,
        public readonly contents : DocView,
    ) { }
}

type PpTag = string

export class PpCmdTag {
    constructor(
        public readonly blockType : PpTag,
        public readonly contents : DocView,
    ) { }
}

export class PpCmdPrintBreak {
    constructor(
        public readonly nspaces : number,
        public readonly offset : number
    ) { }
}

export class PpCmdForceNewline {
    private tag : 'PpCmdForceNewline'
}

export class PpCmdComment {
    constructor(
        public readonly comments : string[]
    ) { }
}

export function app(d1 : T, d2 : T) : T {
    if (d1 instanceof PpCmdEmpty) { return d2 }
    if (d2 instanceof PpCmdEmpty) { return d1 }

    if (d1 instanceof PpCmdGlue) {
        if (d1.docviews.length === 2) {
            const [l1, l2] = d1.docviews
            if (d2 instanceof PpCmdGlue) {
                const l3 = d2.docviews
                return new PpCmdGlue([l1, l2, ...l3])
            }
            return new PpCmdGlue([l1, l2, d2])
        }
    }

    if (d2 instanceof PpCmdGlue) {
        const l2 = d2.docviews
        return new PpCmdGlue([d1, ...l2])
    }

    if (d1 instanceof PpCmdTag && d2 instanceof PpCmdTag) {
        const [t1, dd1] = [d1.blockType, d1.contents]
        const [t2, dd2] = [d2.blockType, d2.contents]
        if (t1 === t2) { return new PpCmdTag(t1, app(dd1, dd2)) }
    }

    if (d1 instanceof Array || d2 instanceof Array) {
        debugger
    }

    return new PpCmdGlue([d1, d2])
}

export function concat(...args : T[]) : T {
    if (args.length === 0) {
        debugger
        throw args
    }
    if (args.length === 1) { return args[0] }
    const [first, ...rest] = args
    return rest.reduce((acc, elt) => new PpCmdGlue([acc, elt]), first)
}

export function str(s : string)              : T { return new PpCmdString(s) }
export function brk(a : number, b : number)  : T { return new PpCmdPrintBreak(a, b) }
export function fnl()                        : T { return new PpCmdForceNewline() }
export function ws(n : number)               : T { return new PpCmdPrintBreak(n, 0) }
export function comment(l : string[])        : T { return new PpCmdComment(l) }

export function mt()  : T { return new PpCmdEmpty() }
export function spc() : T { return new PpCmdPrintBreak(1, 0) }
export function cut() : T { return new PpCmdPrintBreak(0, 0) }

export function isMt(v : T) : boolean { return v instanceof PpCmdEmpty }

export function h  (n : number, s : T) : T { return new PpCmdBox(new PpHBox(n),   s) }
export function v  (n : number, s : T) : T { return new PpCmdBox(new PpVBox(n),   s) }
export function hv (n : number, s : T) : T { return new PpCmdBox(new PpHVBox(n),  s) }
export function hov(n : number, s : T) : T { return new PpCmdBox(new PpHoVBox(n), s) }
export function t  (            s : T) : T { return new PpCmdBox(new PpTBox(),    s) }

export function tag(t : PpTag, s : T) : T {
    return new PpCmdTag(t, s)
}

export function surround(p : T) : T {
    return hov(1, concat(
        str("("),
        p,
        str(")"),
    ))
}

export function prComma()     : T { return concat(str(','),  spc()) }
export function prSemicolon() : T { return concat(str(';'),  spc()) }
export function prBar()       : T { return concat(str('|'),  spc()) }
export function prSpaceBar()  : T { return concat(str(' |'), spc()) }

function prListSepLastSep<A>(
    noEmpty : boolean,
    sepThunk : () => T,
    lastSepThunk : () => T,
    elem : (e : A) => T,
    l : ReadonlyArray<A>
) : T {
    const sep = sepThunk()
    const lastSep = lastSepThunk()
    const elems = l.map(elem)
    const filteredElems = noEmpty ? elems.filter(e => !isMt(e)) : elems
    function insertSeps(es : T[]) : T {
        if      (es.length === 0) { return mt() }
        else if (es.length === 1) { return es[0] }
        else if (es.length === 2) {
            const [h, e] = es
            return concat(h, lastSep, e)
        }
        else {
            const [h, t] = [_.head(es) as T, _.tail(es)]
            return concat(h, sep, insertSeps(t))
        }
    }
    return insertSeps(filteredElems)
}

export function prListWithSep<A>(sep : () => T, pr : (t : A) => T, l : ReadonlyArray<A>) : T {
    return prListSepLastSep(false, sep, sep, pr, l)
}
