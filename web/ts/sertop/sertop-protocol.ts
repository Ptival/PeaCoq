import * as AnswerKind from "./answer-kind"
import * as Feedback from "../coq/feedback"
import * as SertopUtils from "./utils"

export class StmFocus {
  constructor(
    public start: number,
    public stop: number,
    public tip: number
  ) { }
}
