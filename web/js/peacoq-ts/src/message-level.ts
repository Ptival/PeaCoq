import * as EditorTab from "./editor-tab";

export default MessageLevel;

export abstract class MessageLevel {
  abstract getAssociatedTab(): EditorTab.EditorTab;
  abstract toString(): string;
}

export class Debug extends MessageLevel {
  debug: string;
  constructor(s) {
    super();
    this.debug = s;
  }
  getAssociatedTab() { return EditorTab.debug; }
  toString() { return "Debug(" + this.debug + ")"; }
}

export class MyError extends MessageLevel {
  constructor() { super(); }
  getAssociatedTab() { return EditorTab.errors; }
  toString() { return "Error"; }
}

export class Info extends MessageLevel {
  constructor() { super(); }
  getAssociatedTab() { return EditorTab.infos; }
  toString() { return "Info"; }
}

export class Notice extends MessageLevel {
  constructor() { super(); }
  getAssociatedTab() { return EditorTab.notices; }
  toString() { return "Notice"; }
}

export class Warning extends MessageLevel {
  constructor() { super(); }
  getAssociatedTab() { return EditorTab.warnings; }
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
