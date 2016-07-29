
declare namespace AceAjax {
  export interface Anchor {
    $insertRight: boolean;
  }
  export interface IEditSession {
    _signal(s: string): void;
  }
  interface Completion {
    caption?: string;
    meta: string;
    score?: number;
    snippet?: string;
    value?: string;
  }
  interface Completer {
    getCompletions: (editor: Editor, session: IEditSession, position: AceAjax.Position, prefix: string, callback: (err: boolean, results: Completion[]) => void) => void;
  }
  export interface Editor {
    completer: any;
    completers: Completer[];
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

// adding delay with selector
declare namespace Rx {
  export interface Observable<T> {
    delay(subscriptionDelay: Observable<any>, delayDurationSelector: (t: T) => Rx.Observable<any>): Observable<T>;
    // a version of filter that lets me cast the type (when filtering with type assertion)
    filter<U>(predicate: (value: T, index: number, source: Observable<T>) => boolean, thisArg?: any): Observable<U>;
    last(): Observable<T>;
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

declare namespace d3 {
  export function select(selector: Object): Selection<any>;
}
