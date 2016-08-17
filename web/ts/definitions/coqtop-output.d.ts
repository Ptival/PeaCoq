interface Left<T> {
  Left: T;
}

interface Right<T> {
  Right: T;
}

type Either<A, B> = Left<A> | Right<B>;

declare namespace CoqtopInput {
  interface IAddPrime extends ICoqtopInput { }
  interface IEditAt extends ICoqtopInput { }
  interface IGoal extends ICoqtopInput { }
  interface IStatus extends ICoqtopInput { }
  interface IQuery extends ICoqtopInput { }
  interface IQueryPrime extends ICoqtopInput { }
}

declare namespace CoqtopOutput {
  type AddPrime = [number, [Either<{}, number>, string]];
  type EditAt = Either<any, [number, [number, number]]>;
}
