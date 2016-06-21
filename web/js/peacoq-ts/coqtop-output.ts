export class NewTip {

}

export class Unfocus {
  constructor(
    public stateId: number
  ) { }
}

export class StmFocus {
  constructor(
    public start: number,
    public stop: number,
    public tip: number
  ) { }
}

export class Focus {
  constructor(
    public focus: StmFocus
  ) {
    
  }
}

export class Ack {
}

export class StmCurId {
  constructor(
    public stateId: number
  ) { }
}

export class StmAdded {
  constructor(
    public stateId: number,
    public location: CoqLocation,
    public tip: NewTip | Unfocus
  ) { }
}

export class StmCanceled {
  constructor(
    public stateId: number
  ) { }
}

export class StmEdited {
  constructor(
    public stateId: number
  ) { }
}

export class ObjList {
  constructor(
    public stateId: number
  ) { }
}

export class CoqExn {
  constructor(
    public stateId: number
  ) { }
}

export class Completed {
}
