import * as F from '../coq/lib/feedback'
import * as S from '../editor/stage'
import * as A from '../sertop/answer'
import * as AK from '../sertop/answer-kind'
import * as SAPI from '../sertop/serapi-protocol'

export namespace Stage {

    export function sentenceBeingProcessed(
        s : Rx.Observable<ISentence<IStage>>
    ) : Rx.Observable<ISentence<IBeingProcessed>> {
        return (s as Rx.Observable<ISentence<any>>).filter(i => i.stage instanceof S.BeingProcessed)
    }

    export function sentenceProcessed(
        s : Rx.Observable<ISentence<IStage>>
    ) : Rx.Observable<ISentence<IProcessed>> {
        return (s as Rx.Observable<ISentence<any>>).filter(i => i.stage instanceof S.Processed)
    }

    export function beingProcessed(
        s : Rx.Observable<IStage>
    ) : Rx.Observable<IBeingProcessed> {
        return (s as Rx.Observable<any>).filter(i => i instanceof S.BeingProcessed)
    }

    export function processed(
        s : Rx.Observable<IStage>
    ) : Rx.Observable<IProcessed> {
        return (s as Rx.Observable<any>).filter(i => i instanceof S.Processed)
    }

}

export namespace Answer {

    export function answer(s : Rx.Observable<A.Answer>) : Rx.Observable<A.Answer.Answer<AK.AnswerKind>> {
        return s.filter<A.Answer.Answer<AK.AnswerKind>>(A.isAnswer)
    }

    export function feedback(s : Rx.Observable<A.Answer>) : Rx.Observable<F.Feedback<F.FeedbackContent>> {
        return s.filter<F.Feedback<F.FeedbackContent>>(A.isFeedback)
    }

    export namespace Answer {

        export function ack(s : Rx.Observable<A.Answer.Answer<AK.AnswerKind>>) : Rx.Observable<A.Answer.Answer<AK.Ack>> {
            return s.filter<A.Answer.Answer<AK.Ack>>(A.isAck)
        }

        export function completed(s : Rx.Observable<A.Answer.Answer<AK.AnswerKind>>) : Rx.Observable<A.Answer.Answer<AK.Completed>> {
            return s.filter<A.Answer.Answer<AK.Completed>>(A.isCompleted)
        }

        export function added(s : Rx.Observable<A.Answer.Answer<AK.AnswerKind>>) : Rx.Observable<A.Answer.Answer<AK.Added>> {
            return s.filter<A.Answer.Answer<AK.Added>>(A.isAdded)
        }

        export function canceled(s : Rx.Observable<A.Answer.Answer<AK.AnswerKind>>) : Rx.Observable<A.Answer.Answer<AK.Canceled>> {
            return s.filter<A.Answer.Answer<AK.Canceled>>(A.isCanceled)
        }

        export function objList(s : Rx.Observable<A.Answer.Answer<AK.AnswerKind>>) : Rx.Observable<A.Answer.Answer<AK.ObjList>> {
            return s.filter<A.Answer.Answer<AK.ObjList>>(A.isObjList)
        }

        export function coqExn(s : Rx.Observable<A.Answer.Answer<AK.AnswerKind>>) : Rx.Observable<A.Answer.Answer<AK.CoqExn>> {
            return s.filter<A.Answer.Answer<AK.CoqExn>>(A.isCoqExn)
        }

    }

}

export namespace Feedback {

    export function message(s : Feedback$<F.FeedbackContent>) : Message$<F.Level> {
        return s.filter<F.Feedback<F.Message<F.Level>>>(F.Feedback.isMessage)
    }

    export function processed(s : Feedback$<F.FeedbackContent>) : Processed$ {
        return s.filter<F.Feedback<F.Processed>>(F.Feedback.isProcessed)
    }

}

export namespace Message {

    export function debug(s : Message$<F.Level>) : Debug$ {
        return s.filter<F.Feedback<F.Message<F.Debug>>>(F.Feedback.isDebug)
    }

    export function error(s : Message$<F.Level>) : Error$ {
        return s.filter<F.Feedback<F.Message<F.Error>>>(F.Feedback.isError)
    }

    export function info(s : Message$<F.Level>) : Info$ {
        return s.filter<F.Feedback<F.Message<F.Info>>>(F.Feedback.isInfo)
    }

    export function notice(s : Message$<F.Level>) : Notice$ {
        return s.filter<F.Feedback<F.Message<F.Notice>>>(F.Feedback.isNotice)
    }

    export function warning(s : Message$<F.Level>) : Warning$ {
        return s.filter<F.Feedback<F.Message<F.Warning>>>(F.Feedback.isWarning)
    }

}

export namespace Cmd {

    export function add(s : Rx.Observable<SAPI.Cmd>) : Rx.Observable<SAPI.Add> {
        return s.filter<SAPI.Add>(SAPI.isAdd)
    }

    export function cancel(s : Rx.Observable<SAPI.Cmd>) : Rx.Observable<SAPI.Cancel> {
        return s.filter<SAPI.Cancel>(SAPI.isCancel)
    }

    export function exec(s : Rx.Observable<SAPI.Cmd>) : Rx.Observable<SAPI.Exec> {
        return s.filter<SAPI.Exec>(SAPI.isExec)
    }

    export function query(s : Rx.Observable<SAPI.Cmd>) : Rx.Observable<SAPI.Query> {
        return s.filter<SAPI.Query>(SAPI.isQuery)
    }

    export function quit(s : Rx.Observable<SAPI.Cmd>) : Rx.Observable<SAPI.Quit> {
        return s.filter<SAPI.Quit>(SAPI.isQuit)
    }

}
