abstract class Reference { }

type QualId = [Array<string>, string]

class Qualid extends Reference {
  constructor(public lQualid : Located<QualId>) {
    super()
  }
}

class Ident extends Reference {
  constructor(public id : Located<string>) {
    super()
  }
}
