class Maybe<T> {}
class Some<T> extends Maybe<T> {
  some: T;
  constructor(t: T) { super(); this.some = t; }
}
class None<T> extends Maybe<T> {}

function MatchFailure(fn: string, o: Object) {
  if (!o) { return "undefined discriminee"; }
  return ("Match failed in " + fn + ", constructor: " + o.constructor.toString());
}

function MissingOverload(fn: string, o: Object) {
  return ("Missing overload " + fn + ", constructor: " + o.constructor.toString());
}
