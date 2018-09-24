abstract class Source {}

class InFile extends Source {
    constructor(
        public readonly file : string,
    ) { super() }
}

class ToplevelInput extends Source {}

export class T {
    constructor(
        public readonly fname        : Source,
        public readonly line_nb      : number,
        public readonly bol_pos      : number,
        public readonly line_nb_last : number,
        public readonly bol_pos_last : number,
        public readonly bp           : number,
        public readonly ep           : number,
    ) {}
}

export function makeLoc(bp : number, ep : number) {
    return new T(ToplevelInput, -1, 0, -1, 0, bp, ep)
}

export function unLoc(loc : T) : [number, number] {
    return [loc.bp, loc.ep]
}

export type Located<A> = [Maybe<T>, A]
