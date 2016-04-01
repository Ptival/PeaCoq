export default GlobSortGen;

export abstract class GlobSortGen<T> { }

class GProp<T> extends GlobSortGen<T> { }

class GSet<T> extends GlobSortGen<T> { }

class GType<T> extends GlobSortGen<T> {
  type: T;
  constructor(t: T) {
    super();
    this.type = t;
  }
}
