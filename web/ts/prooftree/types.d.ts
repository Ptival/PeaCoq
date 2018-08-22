declare namespace ProofTreeTypes {
  type Node = d3.HierarchyPointNode<IProofTreeNode>
  type Link = d3.HierarchyPointLink<IProofTreeNode>

  // Used to be able to put `never` for the last argument, not sure what changed

  type NodeSelection = d3.Selection<d3.BaseType, Node, any, any>
  type LinkSelection = d3.Selection<d3.BaseType, Link, any, any>

  type HTMLElementSelection = d3.Selection<d3.BaseType, {}, any, any>
}
