abstract class GlobSortGen<T> implements IGlobSortGen<T> { }

class GProp<T> extends GlobSortGen<T> { }

class GSet<T> extends GlobSortGen<T> { }

class GType<T> extends GlobSortGen<T> {
  constructor(public type : T) { super() }
}
