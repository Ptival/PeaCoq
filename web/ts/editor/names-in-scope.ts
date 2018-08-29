import { escapeQuotes } from '../sertop/utils'
import { namesInScopeRoute } from '../peacoq/routes'
import { Control } from '../sertop/command'
import { StmAdd, StmQuery, StmCancel } from '../sertop/control-command'
import { Vernac } from '../sertop/query-command';

export function setup(
    doc : ICoqDocument,
    completed$ : Completed$,
    notice$ : Notice$,
    stmAdded$ : StmAdded$
) : Rx.Observable<string[]> {

    doc.debouncedTip$

        .map(tip => {
            return tip
                .bind(t => t.stage.getStateId())
                .caseOf({
                    nothing : () => Rx.Observable.empty<ISertop.ICommand>(),
                    just : sid => {
                        const setSearch = new Control(new StmAdd({}, 'Set Search Output Name Only.', true))

                        const setSearchOutput$ =
                            stmAdded$
                            .filter(a => a.cmdTag === setSearch.tag)
                            .takeUntil(completed$.filter(a => a.cmdTag === setSearch.tag))
                            .map(a => new Control(new StmCancel([a.answer.stateId])))

                        const search = new Control(
                            new StmQuery(
                                { route : namesInScopeRoute },
                                new Vernac(`SearchAbout -"PEACOQ_NAMES_IN_SCOPE".`),
                                true
                            )
                        )
                        // const editAt = new Control(new StmEditAt(sid))

                        const commands$ = Rx.Observable.concat<ISertop.ICommand>([
                            Rx.Observable.of(setSearch),
                            Rx.Observable.of(search),
                            setSearchOutput$,
                        ])

                        return commands$
                        //return Rx.Observable.of<ISertop.ICommand>(setSearch, search, editAt)
                    }
                })
        })

        .subscribe(cmd$ => doc.sendCommands(cmd$))

    return Rx.Observable.create<string[]>(o => {
        notice$.filter(n => n.routeId === namesInScopeRoute)
            .subscribe(n => {
                o.onNext(n.feedbackContent.message.split('\n'))
            })
    })

}
