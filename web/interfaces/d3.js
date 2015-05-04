/* @flow */

declare class D3Selection {
	append(s: string): D3Selection;
	attr(s1: string, s2: string): D3Selection;
	classed(s: string, b: bool): D3Selection;
	insert(s1: string, s2: string): D3Selection;
	on(s: string, f: (e: Event) => void): D3Selection;
	style(s1: string, s2: string): D3Selection;
}

declare class D3Tree < TNode > {
	children(f: (n: TNode) => Array < TNode > ): D3Tree;
	separation(f: (n: TNode) => number): D3Tree;
}

type D3Diagonal < TNode > = {
	(p: {
		source: TNode,
		target: TNode,
	}): string;
	projection: (f: (n: TNode) => Array < number > ) => D3Diagonal;
}

declare class D3 {
	diagonal(): D3Diagonal;
	layout: D3;
	select(d: Element | string): D3Selection;
	svg: D3;
	tree(): D3Tree;
}

declare
var d3: D3;
