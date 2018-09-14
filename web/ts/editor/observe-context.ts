import * as Context from './context'
import * as Stage from './stage'
import * as DebugFlags from '../peacoq/debug-flags'
import { emptyContext } from '../peacoq/peacoq'
import { getContextRoute } from '../peacoq/routes'
import { Vernac } from '../sertop/query-command'

export function setup(
    doc : ICoqDocument,
    notice$ : Notice$,
    stmQuery$ : Query$
) {
    /*
      Feedback comes back untagged, so need the zip to keep track of the relationship
      between input PeaCoqGetContext and the output context...
    */
    Rx.Observable.zip(
        // We want only PeaCoqGetContext happening because a sentence is processed
        stmQuery$
            .filter(q => q.query instanceof Vernac && q.query.vernac === 'PeaCoqGetContext.')
            .filter(q => q.fromAutomation === false),
        notice$.filter(m => m.route === getContextRoute)
    ).subscribe(([cmd, fbk]) => {
        // console.log(cmd, fbk)
        const stateId = cmd.queryOptions.sid
        if (stateId === undefined) {
            debugger
            throw cmd
        }
        const rawContext = fbk.contents.message
        const sentence = doc.getSentenceByStateId(stateId)
        sentence.caseOf<void>({
            nothing : () => { },
            just : sentence => {
                if (!(sentence.stage instanceof Stage.Processed)) { debugger }
                const stage : IProcessed = <any>sentence.stage
                if (DebugFlags.rawPeaCoqContext) { console.log(rawContext) }
                if (rawContext.length === 0) {
                    stage.setContext(emptyContext)
                } else {
                    const context = Context.create(rawContext)
                    stage.setContext(context)
                }
            }
        })
    })
}
