
export function commonAncestor(n1: IProofTreeNode, n2: IProofTreeNode): IProofTreeNode {
  return n1.getParent().caseOf({
    nothing: () => n1,
    just: n1p => n2.getParent().caseOf({
      nothing: () => n2,
      just: n2p => {
        if (n1.id === n2.id) { return n1 }
        if (n1.depth < n2.depth) {
          return commonAncestor(n1, n2p)
        } else if (n1.depth > n2.depth) {
          return commonAncestor(n1p, n2)
        } else {
          return commonAncestor(n1p, n2p)
        }
      }
    })
  })
}
