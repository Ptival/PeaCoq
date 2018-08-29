import * as _ from 'lodash'

export abstract class BlockType { }
export class PpHBox   extends BlockType { constructor(public x : number) { super() } }
export class PpVBox   extends BlockType { constructor(public x : number) { super() } }
export class PpHVBox  extends BlockType { constructor(public x : number) { super() } }
export class PpHoVBox extends BlockType { constructor(public x : number) { super() } }
export class PpTBox   extends BlockType {}

abstract class DocView { }

export type t = DocView

export class PpCmdEmpty extends DocView {}

export class PpCmdString extends DocView {
    constructor(
        public readonly str : string,
    ) { super() }
}

export class PpCmdGlue extends DocView {
    constructor(
        public readonly docviews : DocView[],
    ) { super() }
}

export class PpCmdBox extends DocView {
    constructor(
        public readonly blockType : BlockType,
        public readonly contents : DocView,
    ) {
        super()
    }
}

type PpTag = string

export class PpCmdTag extends DocView {
    constructor(
        public readonly blockType : PpTag,
        public readonly contents : DocView,
    ) {
        super()
    }
}

export class PpCmdPrintBreak extends DocView {
    constructor(
        public readonly nspaces : number,
        public readonly offset : number
    ) {
        super()
    }
}

export class PpCmdForceNewline<T> extends DocView { }

export class PpCmdComment extends DocView {
    constructor(
        public readonly comments : string[]
    ) { super() }
}

export function str(s : string)              : t { return new PpCmdString(s) }
export function brk(a : number, b : number)  : t { return new PpCmdPrintBreak(a, b) }
export function fnl()                        : t { return new PpCmdForceNewline() }
export function ws(n : number)               : t { return new PpCmdPrintBreak(n, 0) }
export function comment(l : string[])        : t { return new PpCmdComment(l) }

export function mt()  : t { return new PpCmdEmpty() }
export function spc() : t { return new PpCmdPrintBreak(1, 0) }
export function cut() : t { return new PpCmdPrintBreak(0, 0) }

export function isMt(v : t) : boolean { return v instanceof PpCmdEmpty }

export function h  (n : number, s : t) : t { return [new PpCmdBox(new PpHBox(n),   s)] }
export function v  (n : number, s : t) : t { return [new PpCmdBox(new PpVBox(n),   s)] }
export function hv (n : number, s : t) : t { return [new PpCmdBox(new PpHVBox(n),  s)] }
export function hov(n : number, s : t) : t { return [new PpCmdBox(new PpHoVBox(n), s)] }
export function t  (            s : t) : t { return [new PpCmdBox(new PpTBox(),    s)] }

export function tag(t : PpTag, s : t) : t {
    return new PpCmdTag(t, s)
}

export function surround(p : t) : t {
    return hov(1, ([] as t[]).concat(
        str("("),
        p,
        str(")"),
    ))
}

function prListSepLastSep(
    noEmpty : boolean,
    sepThunk : () => t,
    lastSepThunk : () => t,
    elem : (e : t) => t,
    l : t[]
) : t {
    const sep = sepThunk()
    const lastSep = lastSepThunk()
    const elems = l.map(elem)
    const filteredElems = noEmpty ? elems.filter(e => !isMt(e)) : elems
    function insertSeps(es : t[]) : t {
        if      (es.length === 0) { return mt() }
        else if (es.length === 1) { return es[0] }
        else if (es.length === 2) {
            const [h, e] = es
            return ([] as t[]).concat(h, lastSep, e)
        }
        else {
            const [h, t] = [_.head(es) as t, _.tail(es)]
            return ([] as t[]).concat(h, sep, insertSeps(t))
        }
    }
    return insertSeps(filteredElems)
}

export function prListWithSep<T>(sep : () => t, pr : (t : T) => t, l : T[]) : t {
    return prListSepLastSep(false, sep, sep, pr, l)
}

export function prBar()      { return ([] as t[]).concat(str('|'), spc()) }
export function prSpaceBar() { return ([] as t[]).concat(str(';'), spc()) }
