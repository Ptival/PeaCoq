import { GlobSortGen } from "./glob-sort-gen";

export type CoqLocation = [number, number];

type LevelInfo = Maybe<string>;
export type GlobLevel = GlobSortGen<LevelInfo>;

type SortInfo = string[];
export type GlobSort = GlobSortGen<SortInfo>;

export type InstanceExpr = Array<GlobLevel>;

export type Located<T> = [CoqLocation, T];
