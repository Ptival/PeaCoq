import * as Pp from '../lib/pp'

export type PpBox
    = PpHB
    | PpHoVB
    | PpHVB
    | PpVB
    | PpTB

export class PpHB   { constructor(public n : number) { } }
export class PpHoVB { constructor(public n : number) { } }
export class PpHVB  { constructor(public n : number) { } }
export class PpVB   { constructor(public n : number) { } }
export class PpTB   {}

export type PpCut
    = PpBrk
    | PpTbrk
    | PpTab
    | PpFnl

export class PpBrk  { constructor(public n1 : number, public n2 : number) { } }
export class PpTbrk { constructor(public n1 : number, public n2 : number) { } }
export class PpTab  {}
export class PpFnl  {}

export function PpCmdOfBox(b : PpBox, s : Pp.t) : Pp.t {
    if (b instanceof PpHB)   { return Pp.h  (b.n, s) }
    if (b instanceof PpHoVB) { return Pp.hov(b.n, s) }
    if (b instanceof PpHVB)  { return Pp.hv (b.n, s) }
    if (b instanceof PpVB)   { return Pp.v  (b.n, s) }
    throw MatchFailure('PpCmdOfBox', b)
}

export function PpCmdOfCut(c : PpCut) : Pp.t {
    if (c instanceof PpFnl)  { return Pp.fnl() }
    if (c instanceof PpBrk)  { return Pp.brk(c.n1, c.n2) }
    throw MatchFailure('PpCmdOfCut', c)
}

export type Unparsing
    = UnpMetaVar
    | UnpBinderMetaVar
    | UnpListMetaVar
    | UnpBinderListMetaVar
    | UnpTerminal
    | UnpBox
    | UnpCut

export class UnpMetaVar {
    constructor(
        public index : number,
        public parenRelation : ParenRelation
    ) { }
}

export class UnpBinderMetaVar {
    constructor(
        public index : number,
        public parenRelation : ParenRelation,
    ) { }
}

export class UnpListMetaVar {
    constructor(
        public index : number,
        public parenRelation : ParenRelation,
        public unparsing : ReadonlyArray<Unparsing>
    ) { }
}

export class UnpBinderListMetaVar {
    constructor(
        public n : number,
        public isOpen : boolean,
        public unparsing : ReadonlyArray<Unparsing>
    ) { }
}

export class UnpTerminal {
    constructor(
        public terminal : string
    ) { }
}

export class UnpBox {
    constructor(
        public box : PpBox,
        public unparsing : ReadonlyArray<Located<Unparsing>>
    ) { }
}

export class UnpCut {
    constructor(public cut : PpCut) { }
}
