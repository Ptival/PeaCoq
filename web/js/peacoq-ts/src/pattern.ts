
export abstract class Pattern { }

export class Anything extends Pattern { }

export class ArrayPattern extends Pattern {
  array: Pattern[];
  constructor(a: Pattern[]) { super(); this.array = a; }
}

export class BinderPattern extends Pattern {
  binder: string;
  constructor(name: string) { super(); this.binder = name; }
}

export class Constructor extends Pattern {
  name: Function;
  fields: Object;
  constructor(name: Function, fields: Object) {
    super();
    this.name = name;
    this.fields = fields;
  }
}

export class StringPattern extends Pattern {
  string: string;
  constructor(s: string) { super(); this.string = s; }
}
