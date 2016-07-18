
function makeGroup(name: string, tactics: string[]): TacticGroup {
    return {
        "name": name,
        "tactics": _(tactics).map(function(s) { return s + '.'; }).value(),
    };
}

/*
  This strategy tries many tactics, not trying to be smart.
*/
export function tacticsToTry(context: PeaCoqContext, fgIndex: number): TacticGroup[] {

    const hyps = context.fgGoals[fgIndex].ppgoal.hyps;
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
