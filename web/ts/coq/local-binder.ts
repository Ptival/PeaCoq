// import BinderKind from './binder-kind'
// declare class ConstrExpr {}
// import NameBase from './name-base'

abstract class LocalBinder { }

class LocalRawDef extends LocalBinder {
  constructor(
    public binderName : Located<NameBase>,
    public binderType : ConstrExpr
  ) {
    super()
  }
}

class LocalRawAssum extends LocalBinder {
  constructor(
    public names : Array<Located<NameBase>>,
    public binderKind : BinderKind,
    public term : ConstrExpr
  ) {
    super()
  }
}

function beginOfBinder(b : LocalBinder) : number {
  if (b instanceof LocalRawDef) {
    return b.binderName[0][0]
  }
  if (b instanceof LocalRawAssum) {
    return b.names[0][0][0]
  }
  throw MatchFailure('beginOfBinder', b)
}

function beginOfBinders(bl : LocalBinder[]) {
  if (bl.length === 0) { return 0 }
  else { return beginOfBinder(bl[0]) }
}
