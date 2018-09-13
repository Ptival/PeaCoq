import * as AnswerKind from './answer-kind'
import * as Feedback from '../coq/lib/feedback'

export type Answer
    = Answer.Answer<AnswerKind.AnswerKind>
    | Feedback.Feedback<Feedback.FeedbackContent>

export namespace Answer {

    export class Answer<T extends AnswerKind.AnswerKind> {
        constructor(
            public cmdTag : string,
            public answer : T
        ) { }
    }

}

export function isAnswer  (a : Answer) : a is Answer.Answer<AnswerKind.AnswerKind>        { return a instanceof Answer.Answer     }
export function isFeedback(a : Answer) : a is Feedback.Feedback<Feedback.FeedbackContent> { return a instanceof Feedback.Feedback }

export function isAck      (a : Answer.Answer<AnswerKind.AnswerKind>) : a is Answer.Answer<AnswerKind.Ack>       { return AnswerKind.isAck      (a.answer) }
export function isCompleted(a : Answer.Answer<AnswerKind.AnswerKind>) : a is Answer.Answer<AnswerKind.Completed> { return AnswerKind.isCompleted(a.answer) }
export function isAdded    (a : Answer.Answer<AnswerKind.AnswerKind>) : a is Answer.Answer<AnswerKind.Added>     { return AnswerKind.isAdded    (a.answer) }
export function isCanceled (a : Answer.Answer<AnswerKind.AnswerKind>) : a is Answer.Answer<AnswerKind.Canceled>  { return AnswerKind.isCanceled (a.answer) }
export function isObjList  (a : Answer.Answer<AnswerKind.AnswerKind>) : a is Answer.Answer<AnswerKind.ObjList>   { return AnswerKind.isObjList  (a.answer) }
export function isCoqExn   (a : Answer.Answer<AnswerKind.AnswerKind>) : a is Answer.Answer<AnswerKind.CoqExn>    { return AnswerKind.isCoqExn   (a.answer) }

export function create(o : any) : Answer {
    const [name, ...args] = o
    switch (o[0]) {
        case 'Answer' :
            // console.log('RCV', o)
            const [cmdTag, answerKind] = args
            return new Answer.Answer(cmdTag, AnswerKind.create(answerKind))
        case 'Feedback' :
            return Feedback.Feedback.fromSertop(o)
        default :
            debugger
    }
    debugger
    throw 'Answer.create'
}
