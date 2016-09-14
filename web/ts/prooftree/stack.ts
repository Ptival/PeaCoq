export class ProofTreeStack implements IProofTreeStack {
  public added$: Rx.Subject<IProofTree>
  public length: number
  public removed$: Rx.Subject<IProofTree>
  private proofTrees: IProofTree[]

  constructor() {
    this.proofTrees = []
    this.added$ = new Rx.Subject<IProofTree>()
    this.removed$ = new Rx.Subject<IProofTree>()
    this.length = 0
    this.added$.subscribe(() => { this.length++ })
    this.removed$.subscribe(t => {
      t.cleanup()
      this.length--
    })
  }

  public peek(): IProofTree {
    if (this.proofTrees.length === 0) { debugger }
    return this.proofTrees[0]
  }

  public pop(): IProofTree {
    const t = this.proofTrees.shift()
    if (t === undefined) {
      debugger
      throw this
    }
    this.removed$.onNext(t)
    return t
  }

  public push(t: IProofTree): void {
    this.proofTrees.unshift(t)
    this.added$.onNext(t)
  }

}
