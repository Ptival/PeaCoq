export type Pattern
    = Anything
    | ArrayPattern
    | BinderPattern
    | Constructor
    | StringPattern

export class Anything {
    private tag : 'Anything'
}

export class ArrayPattern {
  constructor(public array : Pattern[]) { }
}

export class BinderPattern {
  constructor(public binder : string) { }
}

export class Constructor {
  constructor(public name : Function, public fields : Object) { }
}

export class StringPattern {
  constructor(public str : string) { }
}
