
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
}

// TODO: remove when
// https://github.com/DefinitelyTyped/DefinitelyTyped/pull/9148
// gets merged
declare namespace W2UI {
  interface W2Event {
    onComplete: () => void;
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
