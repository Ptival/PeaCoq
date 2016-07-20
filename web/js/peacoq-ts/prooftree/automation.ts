import * as Context from "../editor/context";
import * as Command from "../sertop/command";
import * as ControlCommand from "../sertop/control-command";

interface ProofTreeAutomationInput {
  completed$;
  doc: ICoqDocument;
  error$: Rx.Observable<ErrorMessageFeedback>;
  notice$: Rx.Observable<NoticeMessageFeedback>;
  queryForTacticToTry$: Rx.Observer<CommandStreamItem>;
  sentenceToDisplay$: Rx.Observable<ISentence<IStage>>;
  stmAdded$: Rx.Observable<ISertop.IAnswer<ISertop.IStmAdded>>;
  stopAutomationRound$: Rx.Observable<{}>;
}

const tacticAutomationRouteId = 2;

export function setup(i: ProofTreeAutomationInput): void {

  const {
    completed$,
    doc,
    error$,
    notice$,
    queryForTacticToTry$,
    sentenceToDisplay$,
    stmAdded$,
    stopAutomationRound$,
  } = i;

  const processedSentenceToDisplay$ =
    sentenceToDisplay$.concatMap(s => s.waitUntilProcessed());

  const contextToDisplay$ =
    processedSentenceToDisplay$
      .concatMap(
      sentence => sentence.stage.getContext(),
      (sentence, context) => ({ context, sentence })
      );

  const setOfTacticsToTry$ =
    contextToDisplay$
      .map(({ context, sentence }) => ({
        context, sentence,
        tactics: (
          context.fgGoals.length === 0
            ? []
            : _(tacticsToTry(context.fgGoals[0])).flatMap(group =>
              group.tactics.map(tactic =>
                ({ context, group: group.name, tactic, sentence })
              )
            ).value()
        ),
      }));

  // every time there is a set of tactics to try, we go through them one by one
  setOfTacticsToTry$
    .subscribe(({ context, sentence, tactics }) => {
      const readyToSendNextCandidate$ = new Rx.Subject<{}>();

      Rx.Observable
        .zip(
        Rx.Observable.fromArray(tactics),
        readyToSendNextCandidate$
        )
        .takeUntil(stopAutomationRound$)
        .subscribe(([{ context: previousContext, group, tactic, sentence }, {}]) => {

          const stateId = sentence.stage.stateId;
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
          stmAddErrored$.subscribe(_ => readyToSendNextCandidate$.onNext({}));
          addNotice$.subscribe(_ => readyToSendNextCandidate$.onNext({}));
          addNotice$
            .subscribe(n => {
              const context = Context.create(n.feedbackContent.message);
              // we only add tactics that change something
              if (!_.isEqual(context, previousContext)) {
                sentence.addCompletion(tactic, group, context);
              }
            });
          const editAt = new Command.Control(new ControlCommand.StmEditAt(stateId));
          const commandStreamItem = Rx.Observable.concat<ISertop.ICommand>([
            Rx.Observable.just(add),
            getContext$,
            Rx.Observable.just(editAt)
          ]).share();
          queryForTacticToTry$.onNext(commandStreamItem);

        });

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
  const curHyps = _(curHypsFull).map(function(h) { return h.name; });
  // TODO: there is a better way to do this
  const curNames = []; // _(curHyps).union(namesPossiblyInScope.reverse());

  const res = [

    // makeGroup(
    //     "terminators",
    //     (pt.goalIsReflexive() ? ["reflexivity"] : [])
    //         .concat([
    //             "discriminate",
    //             "assumption",
    //             "eassumption",
    //         ])
    // ),

    makeGroup(
      "autos",
      ["auto", "eauto"]
    ),

    makeGroup(
      "introductions",
      ["intros", "intro"]
    ),

    makeGroup(
      "break_if, f_equal, subst",
      [
        "break_if",
        "f_equal",
        "repeat f_equal",
        "subst"
      ]
    ),

    // makeGroup(
    //     "simplifications",
    //     ["simpl"].concat(
    //         _(curHyps).map(function(h) { return "simpl in " + h; }).value()
    //     ).concat(
    //         (pt.curNode.hyps.length > 0 ? ["simpl in *"] : [])
    //     )
    // ),
    //
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

    // makeGroup(
    //     "inductions",
    //     _(curHypsFull)
    //         .filter(function(h) {
    //             return h.hType.tag === "Var" && h.hType.contents === "natlist";
    //         })
    //         .map(function(h) { return "induction " + h.hName; })
    //         .value()
    // ),

    makeGroup(
      "inversions",
      _(curHyps).map(function(h) { return "inversion " + h; }).value()
    ),

    makeGroup(
      "solvers",
      ["congruence", "omega", "firstorder"]
    ),

    makeGroup(
      "applications",
      _(curNames).map(function(n) { return "apply " + n; }).value()
        .concat(
        _(curNames).map(function(n) { return "eapply " + n; }).value()
        )
    ),

    // makeGroup(
    //     "rewrites",
    //     _(curNames)
    //         .map(function(n) {
    //             return ["rewrite -> " + n, "rewrite <- " + n];
    //         })
    //         .flatten(true).value()
    // ),
    //
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
      "reverts",
      _(curHyps).map(function(h) { return "revert " + h; }).value()
    ),

  ];

  return res;

}
