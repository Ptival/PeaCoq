
class Exception implements IException {
  constructor(
    public message: string
  ) { }
  getMessage() {
    return this.message;
  }
}

class EvaluatedError implements IException {
  constructor(
    public message: any,
    public exception: Maybe<any>
  ) { }
  getMessage() {
    return this.message;
  }
}

export function create(kind: string, o: any[]): IException {
  switch (kind) {
    case "Cerrors.EvaluatedError":
      switch (o.length) {
        case 1: return new EvaluatedError(o[0], nothing());
        case 2: return new EvaluatedError(o[0], just(o[1]));
        default: debugger;
      }
    default:
    switch (o.length) {
      case 0: return new Exception(o[0]);
      default: debugger;
    }
  }
  debugger;
}
