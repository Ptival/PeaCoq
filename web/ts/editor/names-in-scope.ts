import { escapeQuotes } from '../sertop/utils'
import { namesInScopeRoute } from '../peacoq/routes'
import { Vernac } from '../sertop/query-command'
import { Add, Cancel, Query, Cmd } from '../sertop/serapi-protocol'

export function setup(
    doc : ICoqDocument,
    completed$ : Completed$,
    notice$ : Notice$,
    stmAdded$ : Added$
) : Rx.Observable<string[]> {

    const setSearch = new Add({}, 'Set Search Output Name Only.', true)

    const setSearchOutput$ =
        stmAdded$
        .filter(a => a.cmdTag === setSearch.tag)
        .takeUntil(completed$.filter(a => a.cmdTag === setSearch.tag))
        .map(a => new Cancel([a.answer.stateId]))

    const search = new Query(
        { route : namesInScopeRoute },
        new Vernac(`SearchAbout -"PEACOQ_NAMES_IN_SCOPE".`),
        true
    )
    // const editAt = new Control(new StmEditAt(sid))

    const commands$$ : Rx.Observable<Rx.Observable<Cmd>> = doc.debouncedTip$

        .map(tip => {
            return tip
                .bind(t => t.stage.getStateId())
                .caseOf({
                    nothing : () => Rx.Observable.empty<Cmd>(),
                    just : sid => {

                        const commands$ = Rx.Observable.concat<Cmd>([
                            Rx.Observable.of(setSearch),
                            Rx.Observable.of(search),
                            setSearchOutput$,
                        ])

                        return commands$
                        //return Rx.Observable.of<ISertop.ICommand>(setSearch, search, editAt)
                    }
                })
        })

    /* NOTE:
     * I am not sure which of these two indicate that the query has finished outputting:
     * (Answer <id> Completed)                           where <id> is the id of the (Query ...)
     * (Feedback (... (route <r>)) (contents Processed)) where <r> is the route we use for those queries
     * For now, I will assume it is the former, but if some names faile to appear, it might
     * indicate that we should look for the latter instead.
     * */

    // registering the observable before trigerring the subscription
    const namesInScope$ =
        notice$
        .takeUntil(completed$.filter(a => a.cmdTag === search.tag))
        .filter(n => n.route === namesInScopeRoute)
        .map(n => n.contents.message)
        .toArray()

    commands$$.subscribe(cmd$ => doc.sendCommands(cmd$))

    return namesInScope$

}
