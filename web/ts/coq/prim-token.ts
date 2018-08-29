abstract class PrimToken { }

class Numeral extends PrimToken {
    constructor(
        public readonly raw  : string,
        public readonly sign : boolean,
    ) { super() }
}

class PrimTokenString extends PrimToken {
    constructor(
        public readonly str : string,
    ) { super() }
}
