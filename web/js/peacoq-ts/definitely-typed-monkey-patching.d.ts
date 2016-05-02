
declare module AceAjax {
  export interface Anchor {
    $insertRight: boolean;
  }
  export interface IEditSession {
    _signal(s: string): void;
  }
}

// TODO: remove when
// https://github.com/DefinitelyTyped/DefinitelyTyped/pull/9148
// gets merged
declare namespace W2UI {
  interface W2Event {
    onComplete: () => void;
  }
}

declare namespace Rx {
  export interface Observable<T> extends IObservable<T> {
    flatMapLatest<TResult>(selector: (value: T, index: number, source: Observable<T>) => IPromise<TResult>, thisArg?: any): Observable<TResult>;	// alias for selectSwitch
  }
}
