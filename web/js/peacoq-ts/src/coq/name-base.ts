abstract class NameBase { }

class Name extends NameBase {
  id: string;
  constructor(id: string) {
    super();
    this.id = id;
  }
}

class Anonymous extends NameBase { }
