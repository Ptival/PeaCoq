import { Located } from "./coq-definitions";

export default Reference;

export abstract class Reference { }

type QualId =[Array<string>, string];

class Qualid extends Reference {
  lQualid: Located<QualId>;
  constructor(q: Located<QualId>) {
    super();
    this.lQualid = q;
  }
}

class Ident extends Reference {
  id: Located<string>;
  constructor(id: Located<string>) {
    super();
    this.id = id;
  }
}
