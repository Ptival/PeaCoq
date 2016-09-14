
export abstract class Pattern { }

export class Anything extends Pattern { }

export class ArrayPattern extends Pattern {
  constructor(public array: Pattern[]) { super() }
}

export class BinderPattern extends Pattern {
  constructor(public binder: string) { super() }
}

export class Constructor extends Pattern {
  constructor(public name: Function, public fields: Object) { super() }
}

export class StringPattern extends Pattern {
  constructor(public str: string) { super() }
}
