export default StrToken;

export abstract class StrToken { }

export class StrDef extends StrToken {
  constructor(public string: string) { super(); }
}

export class StrLen extends StrToken {
  constructor(public string: string, public length: number) { super(); }
}
