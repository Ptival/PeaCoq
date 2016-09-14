export class Debug implements IMessageLevel.IDebug { }

export class Error implements IMessageLevel.IError { }

export class Info implements IMessageLevel.IInfo { }

export class Notice implements IMessageLevel.INotice { }

export class Warning implements IMessageLevel.IWarning { }

export function create(s: string): IMessageLevel {
  switch (s) {
    case "Debug": return new Debug()
    case "Error": return new Error()
    case "Info": return new Info()
    case "Notice": return new Notice()
    case "Warning": return new Warning()
    default:
      debugger
      throw s
  }
}
