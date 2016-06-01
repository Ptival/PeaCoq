import * as Global from "./../global-variables";

export class Debug implements IMessageLevel  {
  constructor(
    public debug: string
  ) { }
  toString() { return "Debug(" + this.debug + ")"; }
}

export class Error implements IMessageLevel {
  toString() { return "Error"; }
}

export class Info implements IMessageLevel {
  toString() { return "Info"; }
}

export class Notice implements IMessageLevel {
  toString() { return "Notice"; }
}

export class Warning implements IMessageLevel {
  toString() { return "Warning"; }
}

export function mkMessageLevel(m): IMessageLevel {
  switch (m.tag) {
    case "Debug":
      return new Debug(m.contents);
    case "Error":
      return new Error();
    case "Info":
      return new Info();
    case "Notice":
      return new Notice();
    case "Warning":
      return new Warning();
    default:
      throw `Unknown message level: ${m.tag}`;
  };
}
