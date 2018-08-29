import * as Pp from '../lib/pp'

export abstract class PpBox {}
export class PpHB   extends PpBox { constructor(public n : number) { super() } }
export class PpHoVB extends PpBox { constructor(public n : number) { super() } }
export class PpHVB  extends PpBox { constructor(public n : number) { super() } }
export class PpVB   extends PpBox { constructor(public n : number) { super() } }
export class PpTB   extends PpBox {}

export abstract class PpCut {}
export class PpBrk  extends PpCut { constructor(public n1 : number, public n2 : number) { super() } }
export class PpTbrk extends PpCut { constructor(public n1 : number, public n2 : number) { super() } }
export class PpTab  extends PpCut {}
export class PpFnl  extends PpCut {}

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

export abstract class Unparsing { }

export class UnpMetaVar extends Unparsing {
    constructor(
        public index : number,
        public parenRelation : ParenRelation
    ) {
        super()
    }
}

export class UnpBinderMetaVar extends Unparsing {
    constructor(
        public index : number,
        public parenRelation : ParenRelation,
    ) {
        super()
    }
}

export class UnpListMetaVar extends Unparsing {
    constructor(
        public index : number,
        public parenRelation : ParenRelation,
        public unparsing : Unparsing[]
    ) {
        super()
    }
}

export class UnpBinderListMetaVar extends Unparsing {
    constructor(
        public n : number,
        public isOpen : boolean,
        public unparsing : Unparsing[]
    ) {
        super()
    }
}

export class UnpTerminal extends Unparsing {
    constructor(
        public terminal : string
    ) {
        super()
    }
}

export class UnpBox extends Unparsing {
    constructor(
        public box : PpBox,
        public unparsing : Unparsing[]
    ) {
        super()
    }
}

export class UnpCut extends Unparsing {
    constructor(public cut : PpCut) {
        super()
    }
}
