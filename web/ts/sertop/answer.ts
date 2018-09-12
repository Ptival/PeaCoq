import * as AnswerKind from './answer-kind'
import * as Feedback from '../coq/feedback'

export class Answer implements ISertop.IAnswer<ISertop.IAnswerKind> {
    constructor(
        public cmdTag : string,
        public answer : ISertop.IAnswerKind
    ) { }
}

export function create(o : any) : Answer | Feedback.Feedback {
    const [name, ...args] = o
    switch (o[0]) {
        case 'Answer' :
            // console.log('RCV', o)
            const [cmdTag, answerKind] = args
            return new Answer(cmdTag, AnswerKind.create(answerKind))
        case 'Feedback' :
            return Feedback.fromSertop(o)
        default :
            debugger
    }
    debugger
    throw 'Answer.create'
}
