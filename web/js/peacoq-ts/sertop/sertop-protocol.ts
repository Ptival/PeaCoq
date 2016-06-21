import * as Feedback from "../coq/feedback";

export class Answer {
  constructor(
    public cmdTag: string,
    public answer: IAnswerKind
  ) { }
}

export function mkAnswer(o): Answer | Feedback.Feedback {
  const [name, ...args] = o;
  switch (o[0]) {
    case "Answer":
      const [cmdTag, answerKind] = args;
      return new Answer(cmdTag, mkAnswerKind(answerKind));
    case "Feedback":
      return Feedback.fromSertop(o);
  }
}

export class StmFocus {
  constructor(
    public start: number,
    public stop: number,
    public tip: number
  ) { }
}

export class NewTip { }

namespace AnswerKind {
  export class Ack implements IAnswerKind {
  }
  export class StmEdited implements IAnswerKind {
    constructor(
      public tip: NewTip // | Focus
    ) { }
  }
}

/*
"Ack"
["StmEdited", tip]
*/
function mkAnswerKind(o): IAnswerKind {
  const args = o.slice(1);
  if (o === "Ack") { return new AnswerKind.Ack(); }
  switch (o[0]) {
    case "StmEdited":
      const [tip] = args;
      if (tip === "NewTip") {
        return new AnswerKind.StmEdited(new NewTip());
      } else {
        throw "TODO";
      }
  }
}
