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
