import { Maybe } from 'tsmonad'

import { ProofTreeNode } from './prooftreenode'

function fake(f : FakeNode) : never {
    debugger
    throw f
}

export class FakeNode extends ProofTreeNode implements IFakeNode {
    constructor(p : IProofTree, parent : IProofTreeNode) {
        super(p, Maybe.just(parent))
    }

    public click() : void { return fake(this) }
    public focus() : void { return fake(this) }
    public getAllDescendants() : IProofTreeNode[] { return fake(this) }
    public getAllGoalDescendants() : IGoalNode[] { return fake(this) }
    public getFocusedChild() : Maybe<IProofTreeNode> { return fake(this) }
    public getGoalAncestor() : Maybe<IGoalNode> { return fake(this) }
    public getHeight() : number { return fake(this) }
    public getParent() : Maybe<IProofTreeNode> { return fake(this) }
    public getViewChildren() : IProofTreeNode[] { return fake(this) }
    public getViewFocusedChild() : Maybe<IProofTreeNode> { return fake(this) }
    public getWidth() : number { return fake(this) }
    public isSolved() : boolean { return fake(this) }
}
