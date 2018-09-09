export class Debug implements IMessageLevel.IDebug {
    private tag : 'Debug'
}

export class Error implements IMessageLevel.IError {
    private tag : 'Error'
}

export class Info implements IMessageLevel.IInfo {
    private tag : 'Info'
}

export class Notice implements IMessageLevel.INotice {
    private tag : 'Notice'
}

export class Warning implements IMessageLevel.IWarning {
    private tag : 'Warning'
}

export function create(s : string) : IMessageLevel {
  switch (s) {
    case 'Debug'   : return new Debug()
    case 'Error'   : return new Error()
    case 'Info'    : return new Info()
    case 'Notice'  : return new Notice()
    case 'Warning' : return new Warning()
    default :
      debugger
      throw s
  }
}
