export default Explicitation;

export abstract class Explicitation {}

export class ExplByPos extends Explicitation {
  number: number;
  name: Maybe<string>;
  constructor(n: number, id: Maybe<string>) {
    super();
    this.number = n;
    this.name = id;
  }
}

export class ExplByName extends Explicitation {
  name: string;
  constructor(id: string) {
    super();
    this.name = id;
  }
}
