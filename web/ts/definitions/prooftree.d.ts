type ProofTreeLink = d3.svg.diagonal.Link<IProofTreeNode>

interface TacticGroup {
  name: string
  tactics: string[]
}

interface IStrictly { }

declare type WorklistItem = () => Promise<TacticGroup[]>
declare type XY = { x: number; y: number; }

interface Hypothesis {
  div: HTMLElement
  hName: string
  hValue: string
  hType: string
}
