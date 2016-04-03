export default StrToken;

export abstract class StrToken { }

export class StrDef extends StrToken {
  string: string;
  constructor(s: string) {
    super();
    this.string = s;
  }
}

export class StrLen extends StrToken {
  string: string;
  length: number;
  constructor(s: string, l: number) {
    super();
    this.string = s;
    this.length = l;
  }
}
