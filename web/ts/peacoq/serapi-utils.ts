import * as Answer from '../sertop/answer'
import { Cmd } from '../sertop/serapi-protocol'

export function listenAnswerForCommand<T extends { cmdTag : string }>(
    cmd : Cmd,
    listened$ : Rx.Observable<T>,
    completed$ : Completed$,
) : Rx.Observable<T> {
    return (
        listened$
            .filter(a => a.cmdTag === cmd.cmdTag)
            .takeUntil(completed$.filter(a => a.cmdTag === cmd.cmdTag))
    )
}

interface F {
    catch: () => void
    do: () => void
    each: () => void
    else: () => void
    if: () => void
    finally: () => void
    then: () => void
}

function test(f : F) {
    return (
        f.catch()
            )
    return (
        f.do()
            )
    return (
        f.each()
    )
    return (
        f.else()
            )
    return (
        f.if()
            )
    return (
        f.finally()
            )
    return (
        f.then()
    )
}
