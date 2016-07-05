
declare module AceAjax {
  export interface Anchor {
    $insertRight: boolean;
  }
  export interface IEditSession {
    _signal(s: string): void;
  }
}

// JQuery-UI
interface JQuery {
  draggable(options: Object): JQuery;
  resizable(options: Object): JQuery;
}

declare namespace Rx {
  export interface Observable<T> extends IObservable<T> {
    flatMapLatest<TResult>(selector: (value: T, index: number, source: Observable<T>) => IPromise<TResult>, thisArg?: any): Observable<TResult>;	// alias for selectSwitch
  }
  export interface IPromise<T> {
    catch(handler: (exception: any) => IPromise<T>): IPromise<T>;
  }
}

interface JQueryContextMenuBuildOptions {
  selector: string;
  trigger?: string;
  build: (trigger: JQuery, event: Event) => boolean | any;
}

interface JQueryStatic {
  contextMenu(options: JQueryContextMenuBuildOptions): JQuery;
}

declare var sexpParse: (o: any) => any;

// adding filter with cast
declare namespace Rx {
  export interface Observable<T> extends IObservable<T> {
    filter<U>(predicate: (value: T, index: number, source: Observable<T>) => boolean, thisArg?: any): Observable<U>;
  }
}

declare module _ {
  interface LoDashStatic {
    maxBy<T>(
      collection: List<T>,
      iteratee?: ListIterator<T, number>,
      thisArg?: any
    ): T;
  }
}
