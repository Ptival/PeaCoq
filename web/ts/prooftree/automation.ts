import * as _ from 'lodash'

import * as Feedback from '../coq/lib/feedback'
import * as Context from '../editor/context'
import { tacticAutomationRoute } from '../peacoq/routes'
import { Vernac } from '../sertop/query-command'
import * as SerAPIProtocol from '../sertop/serapi-protocol'

interface ProofTreeAutomationInput {
    commandObserver : Rx.Observer<Command$>
    completed$ : Completed$
    doc : ICoqDocument
    error$ : Error$
    notice$ : Notice$
    stmActionsInFlightCounter$ : Rx.Observable<number>
    stmAdded$ : Added$
    stopAutomationRound$ : Rx.Observable<{}>
}

export function setup(
    completed$ : Completed$,
    doc : ICoqDocument,
    error$ : Error$,
    notice$ : Notice$,
    stmActionsInFlightCounter$ : Rx.Observable<number>,
    stmAdded$ : Added$,
    stopAutomationRound$ : Rx.Observable<{}>
) : void {

    const pause$ = makePause$(stmActionsInFlightCounter$)

    // tip$.subscribe(t => console.log(Date.now(), 'TIP CHANGED'))
    // pause$.subscribe(b => console.log(Date.now(), b ? 'RESUME' : 'PAUSE'))

    doc.debouncedTip$
        .concatMap<ISentence<IStage>>(tip => tip.caseOf({ nothing : () => [], just : s => [s] }))
        .concatMap(sentence => sentence.waitUntilProcessed())
    // Observable<ISentence<IProcessed>>
        .concatMap(
            sentence => sentence.stage.getContext(),
            (sentence, context) => getTacticsForContext(context, sentence)
        )
    // Observable<Tactic[]>
        .map(tactics =>
             Rx.Observable.from(tactics)
             // Observable<tactic>
             .map(tactic => makeCandidate(doc, tactic, completed$, error$, notice$, stmAdded$))
             // Observable<{ commands$, done$ }>
             .concatMap(({ commands$, done$ }) =>
                        Rx.Observable.of(commands$).merge(done$)
                       )
             // Observable<commands$>
            )
    // Observable<Observable<commands$>>
    // ^ one per sentence
    //            ^ one per tactic to try for that sentence
    //                       ^ each tactic involves 3 commands
    // We want to interrupt the tactics for a given sentence when tip$
    // emits, and then start trying for the next sentence.
        .pausableBuffered(pause$) // I don't know why but this is needed for the next pausableBuffered call to work correctly
        .concatMap(candidatesForOneSentence$ =>
                   candidatesForOneSentence$
                   // .do(cs => cs.take(1).subscribe((cmd : Command.Control<ControlCommand.StmAdd>) => console.log(Date.now(), 'Before pause', cmd.controlCommand.sentence)))
                   .pausableBuffered(pause$)
                   // .do(cs => cs.take(1).subscribe((cmd : Command.Control<ControlCommand.StmAdd>) => console.log(Date.now(), 'After pause', cmd.controlCommand.sentence)))
                   .takeUntil(doc.tip$)
                  )
        .subscribe(commands$ => doc.sendCommands(commands$))

}

function makeGroup(name : string, tactics : string[]) : TacticGroup {
    return {
        'name' : name,
        'tactics' : _(tactics).map(s => `${s}.`).value(),
    }
}

/*
  This strategy tries many tactics, not trying to be smart.
*/
function tacticsToTry(e : PeaCoqContextElement) : TacticGroup[] {

    const hyps = e.ppgoal.hyps
    const curHypsFull = _(hyps).clone().reverse()
    const curHyps = curHypsFull.map(h => h.name)
    // TODO : there is a better way to do this
    const curNames = curHyps // _(curHyps).union(namesPossiblyInScope.reverse())

    const res = [

        makeGroup(
            'terminators',
            ([] as string[]).concat(
                // (pt.goalIsReflexive() ? ['reflexivity'] : [])
                ['reflexivity'],
                [
                    'discriminate',
                    'assumption',
                    'eassumption',
                ]
            )
        ),

        makeGroup(
            'automation',
            [
                // 'auto',
                // 'eauto',
            ]
        ),

        makeGroup(
            'introduction',
            ['intros', 'intro']
        ),

        makeGroup(
            'destructuring',
            [
                'break_if',
                'f_equal',
                'repeat f_equal',
                'subst'
            ]
        ),

        makeGroup(
            'simplification',
            ([] as string[]).concat(
                ['simpl'],
                curHyps.map(h => `simpl in ${h}`),
                curHyps.length > 0 ? ['simpl in *'] : []
            )
        ),

        // makeGroup(
        //     'constructors',
        //     (pt.goalIsDisjunction() ? ['left', 'right'] : [])
        //         .concat(pt.goalIsConjunction() ? ['split'] : [])
        //         .concat([
        //             'constructor',
        //             'econstructor',
        //             'eexists',
        //         ])
        // ),
        //
        // makeGroup(
        //     'destructors',
        //     _(curHyps)
        //         .filter(function(h) { return isLowerCase(h[0]); })
        //         .map(function(h) { return 'destruct ' + h; })
        //         .value()
        // ),

        makeGroup(
            'induction',
            curHyps.map(h => `induction ${h}`)
            // This was used for the study because induction applies to everything :(
            // _(curHypsFull)
            //     .filter(function(h) {
            //         return h.hType.tag === 'Var' && h.hType.contents === 'natlist'
            //     })
            //     .map(function(h) { return 'induction ' + h.hName; })
            //     .value()
        ),

        // makeGroup(
        //   'inversion',
        //   curHyps.map(h => `inversion ${h}`)
        // ),

        makeGroup(
            'solver',
            [
                // 'congruence',
                // 'omega',
                // 'firstorder'
            ]
        ),

        makeGroup(
            'application',
            ([] as string[]).concat(
                curNames.map(n => `apply ${n}`),
                curNames.map(n => `eapply ${n}`)
            )
        ),

        makeGroup(
            'rewriting',
            ([] as string[]).concat(
                curNames.map(n => `rewrite -> {n}`),
                curNames.map(n => `rewrite <- {n}`),
            )
        ),

        // makeGroup(
        //     'applications in',
        //     _(curNames).map(function(n) {
        //         return _(curHyps)
        //             .map(function(h) {
        //                 if (h === n) { return []; }
        //                 return ([
        //                     'apply ' + n + ' in ' + h,
        //                     'eapply ' + n + ' in ' + h,
        //                 ])
        //             })
        //             .flatten(true).value()
        //     }).flatten(true).value()
        // ),
        //
        // makeGroup(
        //     'rewrites in',
        //     _(curNames).map(function(n) {
        //         return _(curHyps)
        //             .map(function(h) {
        //                 if (h === n) { return []; }
        //                 return ([
        //                     ('rewrite -> ' + n + ' in ' + h),
        //                     ('rewrite <- ' + n + ' in ' + h)
        //                 ])
        //             })
        //             .flatten(true).value()
        //
        //     }).flatten(true).value()
        // ),

        makeGroup(
            'revert',
            curHyps.map(h => `revert ${h}`)
        ),

    ]

    return res

}

function getTacticsForContext(
    context : PeaCoqContext,
    sentence : ISentence<IProcessed>
) : CandidateInput[] {
    if (context.fgGoals.length === 0) { return [] }
    return (
        _(tacticsToTry(context.fgGoals[0]))
            .flatMap(group =>
                     group.tactics.map(tactic =>
                                       ({ context, group : group.name, tactic, sentence })
                                      )
                    )
            .value()
    )
}

interface CandidateInput {
    context : PeaCoqContext
    group : string
    tactic : string
    sentence : ISentence<IProcessed>
}

// We keep separate commands$ and done$ because we want the recipient to
// be able to send commands$ (atomically) and then immediately send
// other things without waiting for the responses. done$ is used to make
// sure we only try one tactic at a time and stay interruptable between
// two trials.
function makeCandidate(
    doc : ICoqDocument,
    input : CandidateInput,
    completed$ : Completed$,
    error$ : Error$,
    notice$ : Notice$,
    stmAdded$ : Added$
) : {
    commands$ : Rx.Observable<SerAPIProtocol.Cmd>
    done$ : Rx.Observable<any>
} {
    const { context, group, tactic, sentence } = input
    const stateId = sentence.stage.stateId

    // FIXME : not sure how to better do this, but we do not want to send
    // any command if the tip has moved. Somehow, takeUntil(tip$) does not
    // necessarily do a good job, so double-checking here :
    const curSid = _.max(doc.getAllSentences().map(s => s.getStateId().caseOf({ nothing : () => 0, just : sid => sid })))
    if (stateId !== curSid) {
        // console.log('Was expecting', stateId, 'but we are at', curSid, 'aborting')
        return {
            commands$ : Rx.Observable.empty(),
            done$ : Rx.Observable.empty<any>(),
        }
    } else {
        // console.log('Was expecting', stateId, 'and we are at', curSid, 'proceeding')
    }

    const add = new SerAPIProtocol.Add({ ontop : stateId }, tactic, true)
    // listen for the STM added answer (there should be 0 if failed otherwise 1)
    const filteredStmAdded$ = stmAdded$.filter(a => a.cmdTag === add.tag)
        .takeUntil(completed$.filter(a => a.cmdTag === add.tag))
    const getContext$ =
        filteredStmAdded$
        .map(a => new SerAPIProtocol.Query(
            {
                sid : a.answer.stateId,
                // route is used so that the rest of PeaCoq can safely ignore those feedback messages
                route : tacticAutomationRoute
            },
            new Vernac('PeaCoqGetContext.'),
            true
        ))
        .share()

    const stmAddErrored$ = filteredStmAdded$.flatMap(a => error$.filter(e => e.spanId === a.answer.stateId))

    // now, try to pick up the notice feedback for that state id
    const addNotice$ =
        filteredStmAdded$
        .flatMap(a => {
            return notice$
                .filter(n => n.spanId === a.answer.stateId)
                .takeUntil(stmAddErrored$)
                .take(1)
        })
    // we can send the next candidate when we receive either the error or
    // the notice, unless we need to stop.
    addNotice$
        .subscribe(n => {
            const afterContext = Context.create(n.contents.message)
            // we only add tactics that change something
            if (!Context.isEqual(afterContext, context)) {
                sentence.addCompletion(tactic, group, afterContext)
            }
        })
    const editAt = new Control(new StmEditAt(stateId))

    const commands$ = Rx.Observable.concat<SerAPIProtocol.Cmd>([
        Rx.Observable.just(add),
        getContext$,
        Rx.Observable.just(editAt)
    ]).share()

    // this is an empty stream that waits until either stream emits
    const done$ : Message$<Feedback.Level> =
        Rx.Observable.amb<Feedback.Feedback<Feedback.Message<Feedback.Level>>>(stmAddErrored$, addNotice$).take(1).ignoreElements()

    return { commands$, done$ }

}

// Due to the asynchronicity of interactions with coqtop, we may have
// bad races. For instance, we don't want to send a tactic if we sent a
// StmAdd and are about to change state. We cannot rely on tip$ or
// stmAdded$ because we might receive their acknowledgment later. The
// only reliable way is to track pairs of StmAdd-StmAdded and pairs of
// StmCancel-StmCanceled, and to only allow the emission of a
// tactic-to-try when pairs are matched. We also regulate the
// tactic-to-try flow so that only one tactic is being tried at a time,
// so that we can interrupt the flow between any two attempts.
function makePause$(stmActionsInFlightCounter$ : Rx.Observable<number>) : Rx.Observable<boolean> {

    const pause$ = stmActionsInFlightCounter$
    // .do(c => console.log('COUNT', c))
        .map(n => n === 0)
        .startWith(true)
        .distinctUntilChanged()
    // .do(b => console.log('BOOL', b))
    // We need replay because the paused stream will subscribe to pause$
    // later, and it needs to know the last value of pause$ upon
    // subscription. Otherwise, when calling pausableBuffered, the
    // stream will assume false and pause, even though the last value of
    // pause$ was true.
        .replay(false, 1)

    pause$.connect() // make pause$ start running immediately

    return pause$ // .share()

}
