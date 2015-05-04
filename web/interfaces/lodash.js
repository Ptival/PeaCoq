/* @flow */

declare class LodashWrapper < T > {
	contains(sub: string): bool;
	each(f: (t: T, ndx ? : number) => void): LodashWrapper < T > ;
	flatten < R > (b: bool): LodashWrapper < R > ;
	isEmpty(): bool;
	map < R > (f: (t: T, index: number) => R): LodashWrapper < R > ;
	rest(): LodashWrapper < T > ;
	reverse(): LodashWrapper < T > ;
	union(other: Array < T > | LodashWrapper < T > ): LodashWrapper < T > ;
	value(): Array < T > ;
}

type Lodash = { < T > (a: Array < T > ): LodashWrapper < T > ;
	isEqual < R > (t1: R, t2: R): bool;
	partial(f: Function): Function;
	uniqueId(): number;
}

declare
var _: Lodash;
