export abstract class StrToken { }

export class StrDef extends StrToken {
  constructor(public str: string) { super() }
}

export class StrLen extends StrToken {
  constructor(public str: string, public length: number) { super() }
}
