export default GlobSortGen;

export abstract class GlobSortGen<T> implements IGlobSortGen<T> { }

export class GProp<T> extends GlobSortGen<T> { }

export class GSet<T> extends GlobSortGen<T> { }

export class GType<T> extends GlobSortGen<T> {
  type: T;
  constructor(t: T) {
    super();
    this.type = t;
  }
}
