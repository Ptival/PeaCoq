export default StrToken;

export abstract class StrToken { }

class StrDef extends StrToken {
  string: string;
  constructor(s: string) {
    super();
    this.string = s;
  }
}

class StrLen extends StrToken {
  string: string;
  length: number;
  constructor(s: string, l: number) {
    super();
    this.string = s;
    this.length = l;
  }
}
