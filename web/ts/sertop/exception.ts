
class Exception implements IException {
  constructor(
    public message: string
  ) { }
  public getMessage() { return this.message }
}

class EvaluatedError implements IException {
  constructor(
    public message: any,
    public exception: Maybe<any>
  ) { }
  public getMessage() { return this.message }
}

class NoCurrentProof implements IException {
  public getMessage() { return "No current proof." }
}

class UserError implements IException {
  constructor(
    public e: any,
    public message: any
  ) { }
  public getMessage() { return "TODO: UserError" }
}

/*
Listing shapes supported so far:
[["Anomaly: ..."]]
*/
export function create(args: any): IException {
  if (typeof args === "string") {
    switch (args) {
      // case "NoCurrentProof": return new NoCurrentProof()
      default: debugger
    }
  }
  switch (args.length) {
    case 1:
      const [error] = args[0]
      return new Exception(error)
    case 3: {
      const error = args[2][1][1]
      if (error instanceof String) {
        return new Exception(error.toString())
      } else {
        return thisShouldNotHappen()
      }
    }
    default: debugger
  }
  // const [[kind, ...o]] = args
  // if (o[0] === undefined) { debugger }
  // switch (kind) {
  //   case "Cerrors.EvaluatedError":
  //     switch (o.length) {
  //       case 1: return new EvaluatedError(o[0], nothing())
  //       case 2: return new EvaluatedError(o[0], just(o[1]))
  //       default: debugger
  //     }
  //   case "Errors.UserError":
  //     return new UserError(o[0][0], o[0][1])
  //   default:
  //   switch (o.length) {
  //     case 0: return new Exception(o[0])
  //     default: debugger
  //   }
  // }
  debugger
  throw "TODO"
}
