interface Left<T> {
  Left: T;
}

interface Right<T> {
  Right: T;
}

type Either<A, B> = Left<A> | Right<B>;

type EditAt = Either<any, [number, [number, number]]>;

