abstract class GlobSortGen<T> implements IGlobSortGen<T> { }

class GProp<T> extends GlobSortGen<T> {
    private tag : 'GProp'
}

class GSet<T> extends GlobSortGen<T> {
    private tag : 'GSet'
}

class GType<T> extends GlobSortGen<T> {
  constructor(public type : T) { super() }
}
