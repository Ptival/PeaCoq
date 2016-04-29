
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
