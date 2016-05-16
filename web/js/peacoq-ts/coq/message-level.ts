import * as Global from "./../global-variables";

export default MessageLevel;

export abstract class MessageLevel {
  abstract toString(): string;
}

export class Debug extends MessageLevel {
  constructor(
    public debug: string
  ) {
    super();
  }
  toString() { return "Debug(" + this.debug + ")"; }
}

export class MyError extends MessageLevel {
  constructor() { super(); }
  toString() { return "Error"; }
}

export class Info extends MessageLevel {
  constructor() { super(); }
  toString() { return "Info"; }
}

export class Notice extends MessageLevel {
  constructor() { super(); }
  toString() { return "Notice"; }
}

export class Warning extends MessageLevel {
  constructor() { super(); }
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
