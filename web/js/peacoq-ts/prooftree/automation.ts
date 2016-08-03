import * as Context from "../editor/context";
import * as Command from "../sertop/command";
import * as ControlCommand from "../sertop/control-command";

interface ProofTreeAutomationInput {
  stmActionsInFlightCounter$: Rx.Observable<number>;
  completed$;
  doc: ICoqDocument;
  error$: Rx.Observable<ErrorMessageFeedback>;
  notice$: Rx.Observable<NoticeMessageFeedback>;
  queryForTacticToTry$: Rx.Observer<CommandStreamItem<any>>;
  stmAdded$: Rx.Observable<ISertop.IAnswer<ISertop.IStmAdded>>;
  stopAutomationRound$: Rx.Observable<{}>;
  debouncedTip$: Rx.Observable<ISentence<IStage>>;
  tip$: Rx.Observable<ISentence<IStage>>;
}

const tacticAutomationRouteId = 2;

export function setup(i: ProofTreeAutomationInput): void {

  const {
    stmActionsInFlightCounter$,
    completed$,
    doc,
    error$,
    notice$,
    queryForTacticToTry$,
    stmAdded$,
    stopAutomationRound$,
    debouncedTip$,
    tip$,
  } = i;

  const pause$ = makePause$(stmActionsInFlightCounter$);

  debouncedTip$
    .concatMap(sentence => sentence.waitUntilProcessed())
    // sentence-1, ...
    .concatMap(
      sentence => sentence.stage.getContext(),
      (sentence, context) => getTacticsForContext(context, sentence)
    )
    // tactics-for-sentence-1, ...
    .map(tactics =>
      Rx.Observable.fromArray(tactics)
        .map(tactic => makeCandidate(doc, tactic, completed$, error$, notice$, stmAdded$))
    )
    // For each sentence, we have an item.
    // Each item is a stream of candidates, one per tactic to be tried
    // Each candidate is a stream of 3 commands, namely Add, Query, Cancel
    .subscribe(candidatesForASentence$ => {
      // every time a new sentence comes, this stream helps regulate the flow of its candidates
      const readyToSendNextCandidate$ = new Rx.Subject<{}>();
      Rx.Observable
        .zip(candidatesForASentence$, readyToSendNextCandidate$)
        .map(([t, {}]) => t)
        .share()
        .pausableBuffered(pause$)
        .takeUntil(tip$)
        .subscribe(candidate => {
          candidate.done$.subscribe(() => readyToSendNextCandidate$.onNext({}));
          queryForTacticToTry$.onNext(candidate.commandsToTryOneTactic$);
        });
      // start processing candidates for this sentence
      readyToSendNextCandidate$.onNext({});
    });

}

function makeGroup(name: string, tactics: string[]): TacticGroup {
  return {
    "name": name,
    "tactics": _(tactics).map(function(s) { return s + '.'; }).value(),
  };
}

/*
  This strategy tries many tactics, not trying to be smart.
*/
function tacticsToTry(e: PeaCoqContextElement): TacticGroup[] {

  const hyps = e.ppgoal.hyps;
  const curHypsFull = _(hyps).clone().reverse();
  const curHyps = curHypsFull.map(h => h.name);
  // TODO: there is a better way to do this
  const curNames = []; // _(curHyps).union(namesPossiblyInScope.reverse());

  const res = [

    makeGroup(
      "terminators",
      [].concat(
        // (pt.goalIsReflexive() ? ["reflexivity"] : [])
        ["reflexivity"],
        [
          "discriminate",
          "assumption",
          "eassumption",
        ]
      )
    ),

    makeGroup(
      "automation",
      [
        // "auto",
        // "eauto",
      ]
    ),

    makeGroup(
      "introduction",
      ["intros", "intro"]
    ),

    makeGroup(
      "destructuring",
      [
        "break_if",
        "f_equal",
        "repeat f_equal",
        "subst"
      ]
    ),

    makeGroup(
      "simplification",
      [].concat(
        ["simpl"],
        curHyps.map(h => `simpl in ${h}`),
        curHyps.length > 0 ? ["simpl in *"] : []
      )
    ),

    // makeGroup(
    //     "constructors",
    //     (pt.goalIsDisjunction() ? ["left", "right"] : [])
    //         .concat(pt.goalIsConjunction() ? ["split"] : [])
    //         .concat([
    //             "constructor",
    //             "econstructor",
    //             "eexists",
    //         ])
    // ),
    //
    // makeGroup(
    //     "destructors",
    //     _(curHyps)
    //         .filter(function(h) { return isLowerCase(h[0]); })
    //         .map(function(h) { return "destruct " + h; })
    //         .value()
    // ),

    makeGroup(
      "induction",
      curHyps.map(h => `induction ${h}`)
      // This was used for the study because induction applies to everything :(
      // _(curHypsFull)
      //     .filter(function(h) {
      //         return h.hType.tag === "Var" && h.hType.contents === "natlist";
      //     })
      //     .map(function(h) { return "induction " + h.hName; })
      //     .value()
    ),

    // makeGroup(
    //   "inversion",
    //   curHyps.map(h => `inversion ${h}`)
    // ),

    makeGroup(
      "solver",
      [
        // "congruence",
        // "omega",
        // "firstorder"
      ]
    ),

    makeGroup(
      "application",
      [].concat(
        curNames.map(n => `apply ${n}`),
        curNames.map(n => `eapply ${n}`)
      )
    ),

    makeGroup(
      "rewriting",
      [].concat(
        curNames.map(n => `rewrite -> {n}`),
        curNames.map(n => `rewrite <- {n}`),
      )
    ),

    // makeGroup(
    //     "applications in",
    //     _(curNames).map(function(n) {
    //         return _(curHyps)
    //             .map(function(h) {
    //                 if (h === n) { return []; }
    //                 return ([
    //                     "apply " + n + " in " + h,
    //                     "eapply " + n + " in " + h,
    //                 ]);
    //             })
    //             .flatten(true).value();
    //     }).flatten(true).value()
    // ),
    //
    // makeGroup(
    //     "rewrites in",
    //     _(curNames).map(function(n) {
    //         return _(curHyps)
    //             .map(function(h) {
    //                 if (h === n) { return []; }
    //                 return ([
    //                     ("rewrite -> " + n + " in " + h),
    //                     ("rewrite <- " + n + " in " + h)
    //                 ]);
    //             })
    //             .flatten(true).value()
    //         ;
    //     }).flatten(true).value()
    // ),

    makeGroup(
      "revert",
      curHyps.map(h => `revert ${h}`)
    ),

  ];

  return res;

}

function getTacticsForContext(context, sentence) {
  if (context.fgGoals.length === 0) { return []; }
  return (
    _(tacticsToTry(context.fgGoals[0]))
      .flatMap(group =>
        group.tactics.map(tactic =>
          ({ context, group: group.name, tactic, sentence })
        )
      )
      .value()
  );
}

/* This needs to be simplified... */
function makeCandidate(
  doc: ICoqDocument,
  input,
  completed$,
  error$,
  notice$,
  stmAdded$
): {
    commandsToTryOneTactic$: CommandStreamItem<ISertop.ICommand>;
    done$: Rx.Observable<{}>
  } {
  const { context, group, tactic, sentence } = input;
  const stateId = sentence.stage.stateId;

  // FIXME: not sure how to better do this, but we do not want to send
  // any command if the tip has moved. Somehow, takeUntil(tip$) does not
  // necessarily do a good job, so double-checking here:
  const curSid = _.max(doc.getAllSentences().map(s => s.getStateId().caseOf({ nothing: () => 0, just: sid => sid })));
  if (stateId !== curSid) {
    // console.log("Was expecting", stateId, "but we are at", curSid, "aborting");
    return {
      commandsToTryOneTactic$: Rx.Observable.empty<ISertop.ICommand>(),
      done$: Rx.Observable.empty(),
    };
  } else {
    // console.log("Was expecting", stateId, "and we are at", curSid, "proceeding");
  }

  const add = new Command.Control(new ControlCommand.StmAdd({ ontop: stateId }, tactic));
  // listen for the STM added answer (there should be 0 if failed otherwise 1)
  const filteredStmAdded$ = stmAdded$.filter(a => a.cmdTag === add.tag)
    .takeUntil(completed$.filter(a => a.cmdTag === add.tag));
  const getContext$ =
    filteredStmAdded$
      .map(a => new Command.Control(new ControlCommand.StmQuery({
        sid: a.answer.stateId,
        // route is used so that the rest of PeaCoq can safely ignore those feedback messages
        route: tacticAutomationRouteId
      }, "PeaCoqGetContext.")))
      .share();
  const stmAddErrored$ = filteredStmAdded$.flatMap(a => error$.filter(e => e.editOrStateId === a.answer.stateId));
  // now, try to pick up the notice feedback for that state id
  const addNotice$ =
    filteredStmAdded$
      .flatMap(a => {
        return notice$
          .filter(n => n.editOrStateId === a.answer.stateId)
          .takeUntil(stmAddErrored$)
          .take(1)
      });
  // we can send the next candidate when we receive either the error or
  // the notice, unless we need to stop.
  addNotice$
    .subscribe(n => {
      const afterContext = Context.create(n.feedbackContent.message);
      // we only add tactics that change something
      if (!Context.isEqual(afterContext, context)) {
        sentence.addCompletion(tactic, group, afterContext);
      }
    });
  const editAt = new Command.Control(new ControlCommand.StmEditAt(stateId));
  const commandsToTryOneTactic$ = Rx.Observable.concat<ISertop.ICommand>([
    Rx.Observable.just(add),
    getContext$,
    Rx.Observable.just(editAt)
  ]).share();
  return { commandsToTryOneTactic$, done$: Rx.Observable.amb(stmAddErrored$, addNotice$) };

}

/*
Due to the asynchronicity of interactions with coqtop, we may have
bad races. For instance, we don't want to send a tactic if we sent a StmAdd
and are about to change state. We cannot rely on tip$ or stmAdded$ because
we might receive their acknowledgment later. The only reliable way is to
track pairs of StmAdd-StmAdded and pairs of StmCancel-StmCanceled, and to
only allow the emission of a tactic-to-try when pairs are matched.
We also regulate the tactic-to-try flow so that only one tactic is being
tried at a time, so that we can interrupt the flow between any two attempts.
*/
function makePause$(stmActionsInFlightCounter$): Rx.Observable<boolean> {

  const pause$ = stmActionsInFlightCounter$
    .map(n => n === 0)
    .startWith(true)
    .distinctUntilChanged()
    /* We need replay because the paused stream will subscribe to pause$
       later, and it needs to know the last value of pause$ upon subscription.
       Otherwise, when calling pausableBuffered, the stream will assume false
       and pause, even though the last value of pause$ was true.
    */
    .replay();

  pause$.connect(); // make pause$ start running immediately

  return pause$;

}
