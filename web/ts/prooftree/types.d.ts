declare namespace ProofTreeTypes {
  type Node = d3.HierarchyPointNode<IProofTreeNode>
  type Link = d3.HierarchyPointLink<IProofTreeNode>

  type NodeSelection = d3.Selection<d3.BaseType, Node, any, never>
  type LinkSelection = d3.Selection<d3.BaseType, Link, any, never>

  type HTMLElementSelection = d3.Selection<d3.BaseType, {}, any, never>
}
