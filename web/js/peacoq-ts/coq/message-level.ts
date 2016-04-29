/// <reference path="../editor/editor.d.ts"/>

import * as Global from "./../global-variables";

export default MessageLevel;

export abstract class MessageLevel {
  abstract getAssociatedTab(): IEditorTab;
  abstract toString(): string;
}

export class Debug extends MessageLevel {
  constructor(
    public debug: string
  ) {
    super();
  }
  getAssociatedTab() { return Global.tabs.debug; }
  toString() { return "Debug(" + this.debug + ")"; }
}

export class MyError extends MessageLevel {
  constructor() { super(); }
  getAssociatedTab() { return Global.tabs.errors; }
  toString() { return "Error"; }
}

export class Info extends MessageLevel {
  constructor() { super(); }
  getAssociatedTab() { return Global.tabs.infos; }
  toString() { return "Info"; }
}

export class Notice extends MessageLevel {
  constructor() { super(); }
  getAssociatedTab() { return Global.tabs.notices; }
  toString() { return "Notice"; }
}

export class Warning extends MessageLevel {
  constructor() { super(); }
  getAssociatedTab() { return Global.tabs.warnings; }
  toString() { return "Warning"; }
}

export function mkMessageLevel(m): MessageLevel {
  switch (m.tag) {
    case "Debug":
      return new Debug(m.contents);
    case "Error":
      return new MyError();
    case "Info":
      return new Info();
    case "Notice":
      return new Notice();
    case "Warning":
      return new Warning();
    default:
      throw ("Unknown message level: " + m.tag);
  };
}
