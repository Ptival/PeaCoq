export default NameBase;

export abstract class NameBase { }

export class Name extends NameBase {
  id: string;
  constructor(id: string) {
    super();
    this.id = id;
  }
}

export class Anonymous extends NameBase { }
