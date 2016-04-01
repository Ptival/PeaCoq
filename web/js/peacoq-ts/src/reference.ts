import { Located } from "./coq-definitions";

export default Reference;

export abstract class Reference { }

export type QualId =[Array<string>, string];

export class Qualid extends Reference {
  lQualid: Located<QualId>;
  constructor(q: Located<QualId>) {
    super();
    this.lQualid = q;
  }
}

export class Ident extends Reference {
  id: Located<string>;
  constructor(id: Located<string>) {
    super();
    this.id = id;
  }
}
