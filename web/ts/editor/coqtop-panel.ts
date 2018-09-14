import { Maybe } from 'tsmonad'
import * as Feedback from '../coq/lib/feedback'

const maxMessagesOnScreen = 10

export function setup(
    doc : ICoqDocument,
    container : JQuery,
    error$ : Error$,
    notice$ : Notice$,
    loadedFile$ : Rx.Observable<{}>
) {
    const message$ : Rx.Observable<{ message : string; level : PeaCoqMessageLevel }> =
        Rx.Observable.merge(

            error$
            // due to sending sentences fast, we receive errors for states beyond
            // another failed state. reporting those looks spurious to the user.
                .filter(e => Maybe.isJust(doc.getSentenceByStateId(e.spanId)))
                .map(e => ({
                    message : e.contents.message,
                    level : PeaCoqMessageLevel.Danger,
                })),

            notice$
                .filter(e => e.route === 0) // other routes are used by PeaCoq
                .map(e => ({
                    message : e.contents.message,
                    level : PeaCoqMessageLevel.Success,
                }))

        )

    message$.subscribe(({ message, level }) => {
        container.prepend(makeAlert(message, peaCoqMessageLevelToString(level)))
        container.children().slice(maxMessagesOnScreen).remove()
    })
    loadedFile$.subscribe(() => container.empty())

}

function makeAlert(message : string, klass : string) {
    return $('<div>')
        .text(message)
        .addClass(`alert alert-${klass}`)
        .css('font-family', 'monospace')
        .css('margin-bottom', '2px')
        .css('padding', '2px')
        .css('white-space', 'pre')
}

function classify(level : IMessageLevel) : PeaCoqMessageLevel {
    switch (level.constructor) {
        case Feedback.Debug : return PeaCoqMessageLevel.Default
        case Feedback.Error : return PeaCoqMessageLevel.Danger
        case Feedback.Info : return PeaCoqMessageLevel.Info
        case Feedback.Notice : return PeaCoqMessageLevel.Success
        case Feedback.Warning : return PeaCoqMessageLevel.Warning
    }
    throw 'CoqtopPanel.classigy'
}

function peaCoqMessageLevelToString(level : IMessageLevel) : string {
    switch (level) {
        case PeaCoqMessageLevel.Default : return 'default'
        case PeaCoqMessageLevel.Danger : return 'danger'
        case PeaCoqMessageLevel.Info : return 'info'
        case PeaCoqMessageLevel.Success : return 'success'
        case PeaCoqMessageLevel.Warning : return 'warning'
    }
    throw 'CoqtopPanel.peaCoqMessageLevelToString'
}
