import * as AnswerKind from "./answer-kind";
import * as Feedback from "../coq/feedback";

export class Answer implements Sertop.IAnswer<Sertop.IAnswerKind> {
  constructor(
    public cmdTag: string,
    public answer: Sertop.IAnswerKind
  ) { }
}

export function create(o): Answer | Feedback.Feedback {
  const [name, ...args] = o;
  switch (o[0]) {
    case "Answer":
      const [cmdTag, answerKind] = args;
      return new Answer(cmdTag, AnswerKind.create(answerKind));
    case "Feedback":
      return Feedback.fromSertop(o);
  }
}
