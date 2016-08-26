interface IProofTreeStack {
  added$: Rx.Subject<IProofTree>;
  readonly length: number;
  removed$: Rx.Subject<IProofTree>;
  peek(): IProofTree;
  pop(): IProofTree;
  push(t: IProofTree): void;
}
