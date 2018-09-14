import * as Answer from './answer'
import * as AnswerKind from './answer-kind'
import * as SerAPIProtocol from './serapi-protocol'
import * as Feedback from '../coq/lib/feedback'
import * as Filters from '../peacoq/filters'

export function setup(
    cmd$ : Rx.Observable<SerAPIProtocol.Cmd>
) : CoqtopOutputStreams {

    // Need to use something like websockets to avoid having to poll like this
    const pingOutput$ =
        Rx.Observable.interval(250)
        .concatMap(sendPing)
        .concatMap(a => a)
        .share()

    // This will contain a value every time we receive a response
    const cmdOutputSubject = new Rx.Subject<number>()

    // We must slow down cmd$ because server handlers are run in parallel
    // and writes to coqtop are not atomic, so burst of messages become
    // intertwined!...
    const slowedCmd$ =
        Rx.Observable.zip<SerAPIProtocol.Cmd, number>(
            cmd$,
            cmdOutputSubject
        )

    // cmdOutputSubject.subscribe(nb => console.log('ACK', nb))

    const cmdOutput$ =
        slowedCmd$
        .concatMap(([cmd, nb]) => {
            // console.log('SENDING', cmd.tag, cmd)
            return sendCommand(cmd)
        })
        .concatMap(a => a)
        .publish()

    const output$ = Rx.Observable.merge(pingOutput$, cmdOutput$)

    output$
        .filter<Answer.Answer.Answer<AnswerKind.AnswerKind>>(Answer.isAnswer)
        .filter(o => o.answer instanceof AnswerKind.Ack)
    // we don't listen to the answer from `cmdTagMinimum` as it may not arrive
        .filter(o => + o.cmdTag >= SerAPIProtocol.cmdTagMinimum + 1)
        .subscribe(o => { cmdOutputSubject.onNext(+ o.cmdTag) })

    cmdOutput$.connect()
    // So, this is a bit complicated, but we need two freebies :
    // - the first one is the command Quit, whose ACK we may or may not receive
    // - the second one is the first actual command we care to send
    cmdOutputSubject.onNext(-2)
    cmdOutputSubject.onNext(-1)

    const answer$ = output$.let(Filters.Answer.answer)
    const feedback$ = output$.let(Filters.Answer.feedback)
    const messageFeedback$ = feedback$.let(Filters.Feedback.message)
    return {
        answer$s : {
            completed$   : answer$.filter(a => a.answer instanceof AnswerKind.Completed) as any,
            coqExn$      : answer$.filter(a => a.answer instanceof AnswerKind.CoqExn) as any,
            stmAdded$    : answer$.filter(a => a.answer instanceof AnswerKind.Added) as any,
            stmCanceled$ : answer$.filter(a => a.answer instanceof AnswerKind.Canceled) as any,
        },
        feedback$s : {
            message$s : {
                debug$   : messageFeedback$.let(Filters.Message.debug  ),
                error$   : messageFeedback$.let(Filters.Message.error  ),
                info$    : messageFeedback$.let(Filters.Message.info   ),
                notice$  : messageFeedback$.let(Filters.Message.notice ),
                warning$ : messageFeedback$.let(Filters.Message.warning),
            },
            processed$ : feedback$.let(Filters.Feedback.processed),
        },
    }
}

function wrapAjax(i : JQueryAjaxSettings) : Promise<any> {
    return new Promise((onFulfilled, onRejected) => {
        const jPromise = $.ajax(i)
        jPromise.done(o => onFulfilled(o))
        jPromise.fail(e => onRejected(e))
    })
}

function sendPing() : Promise<Answer.Answer.Answer<AnswerKind.AnswerKind>[]> {
    // console.log('PING')
    return (
        wrapAjax({
            type : 'POST',
            url : 'ping',
            data : {},
            async : true,
        })
            .then(r => r.map(sexpParse).map(Answer.create))
        // .catch(e => {
        //     console.log(`PING request failed`)
        //     console.log(`Error:`)
        //     console.log(e)
        //     throw e
        // })
    )
}

function sendCommand(cmd : SerAPIProtocol.Cmd) : Promise<Answer.Answer.Answer<AnswerKind.AnswerKind>[]> {
    console.log('SEND', cmd)
    const datum = `(${cmd.tag} ${cmd.toSexp()})`
    console.log(datum)
    // debugger
    return (
        wrapAjax({
            type : 'POST',
            url : 'coqtop',
            data : datum,
            async : true,
        })
            .then(r => {
                // console.log('RECV', r)
                return r.map(sexpParse).map(Answer.create)
            })
        // .catch(e => {
        //     console.log(`POST request failed:`)
        //     console.log(datum)
        //     console.log(`Error:`)
        //     console.log(e)
        //     throw e
        // })
    ) // FIXME: typescript-mode indentation is wrong
}
