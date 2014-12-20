
function firstSteps(add) {

    add(mkText(
        "<p>Welcome to the world of the Coq proof assistant.</p>"
    ));

    add(mkText(
        p("In this lecture, we will use the following lexicon:")
            + ul(
                li(
                    "A <em>term</em> is any sequence of characters that makes sense in the language we will use to program and prove."
                ) + li (
                    "A <em>type</em> is a way to classify terms. Types can be empty (they don't contain any term), or have a finite or infinite number of terms."
                ) + li (
                    p(
                        "A <em>value</em> is a term obtained after performing all the possible computations."
                    ) + p(
                        "Every term is a value or can be computed down to a value."
                    ) + p(
                        "In particular, the type of a term will remain compatible with the type of its value. A <code>nat</code> (say, <code>2 + 3</code>) stays a <code>nat</code> (<code>5</code>)."
                    )
                )
            )
    ));

    add(mkText(
        "<p>One of the most basic types is the boolean type. A boolean value (a value of type <code>bool</code>) is either the constructor <code>true</code>, or the constructor <code>false</code>.</p><p>Click on the Play button below before you keep reading.</p>"
    ));

    add(mkCoqReadonly(
        "Inductive bool : Type := true | false."
    ));

    add(mkText(
        "<p>Once Coq has registered this new type, we print it again for checking purposes.</p><p>This text says that <code>bool</code> is a new inductive type (a value of type <code>Type</code>), and that there exists (only) two ways to build a value of type <code>bool</code>: one is the value <code>true</code>, and the other is the value <code>false</code>.</p><p>The meaning of <code>Inductive</code> will be explained later on.</p>"
    ));

    add(mkText(
        "<p>Let's prove something right away, a value of type <code>bool</code> can only be equal to <code>true</code> or equal to <code>false</code>.</p><p>Once again, and every time, click on the Play button and interact with the new window before continuing reading.</p>"
    ));

    add(mkCoqReadonly(
        'Theorem bools_are_true_or_false : forall b : bool, b = true \\\/ b = false.',
        function(pt) {
            if (pt.curNode.depth === 0) {
                return ["intro", "admit"];
            } else {
                return ["left", "right", "destruct", "reflexivity"];
            }
        },
        function(pt) {

            switch(pt.curNode.depth) {

            case 0:
                if (!pt.userState.introducedGoal) {
                    pt.userState.introducedGoal = true;
                    var introNode = findTacticByName(pt.curNode.children, "intro");
                    tooltipSequence(pt, [
                        {
                            "node": pt.curNode,
                            "arrowPosition": "left",
                            "contents":
                            "<p>This is your current goal. It is highlighted in green.</p>"
                                + '<p><code>∀</code> means «for all».</p>'
                                + '<p><code>b : bool</code> should be read as «b of type bool».</p>'
                                + p('<code>∨</code> means «or».')
                                + '<p>Therefore, this goal states that for any element <code>b</code> of type <code>bool</code>, either <code>b = true</code> or <code>b = false</code> holds.</p>'
                            ,
                        },
                        {
                            "node": introNode,
                            "arrowPosition": "top",
                            "contents":
                            "<p>This is a tactic node.</p>"
                                + "<p>In order to prove a goal, you will need to pick which tactic "
                                + "to run.</p>"
                                + "<p><code>intro</code> is the only tactic which applies here.</p>"
                                + "<p>It moves the universally-quantified variable <code>b</code> "
                                + "from your goal to your context.</p>"
                            ,
                        },
                        {
                            "node": introNode.children[0],
                            "arrowPosition": "right",
                            "contents":
                            "<p>This is the resulting subgoal.</p>"
                                + "<p>Everything above the horizontal line is your context.</p>"
                                + "<p>You can see the variable <code>b</code> of type "
                                + "<code>bool</code> has been moved from the goal to the "
                                + "context.</p>"
                            ,
                        },
                        {
                            "node": introNode,
                            "arrowPosition": "top",
                            "contents":
                            p("Each tactic either adds, removes, or modifies elements from your context or your goal. Try to understand what each of them does by comparing the state before (on the left) and after (on the right).")
                              + p("You can hover your mouse over a resulting goal (on the right) to get a visual hint as to what has changed from the previous goal (on the left).")
                            ,
                        },
                    ]);
                }
                return;
                break;

            case 2:
                if (!pt.userState.introducedMultipleTactics) {
                    pt.userState.introducedMultipleTactics = true;
                    tooltipSequence(pt, [
                        {
                            "node": pt.curNode.children[2],
                            "arrowPosition": "top",
                            "contents":
                            "<p>There can be more than one tactic applicable to a given goal.</p><p>Some of them might do the wrong thing, so be mindful.</p>"
                            ,
                        },
                        {
                            "node": pt.curNode.parent,
                            "arrowPosition": "top",
                            "contents":
                            "<p>If you made a wrong move, you can always click on the parent tactic to go back up in the tree and change your decision.</p>"
                            ,
                        },
                        {
                            "node": findTacticByName(pt.curNode.children, "left"),
                            "arrowPosition": "top",
                            "contents":
                            "<p>The <code>left</code> tactic should be used when you think the left side of a disjunction is true. You will need to prove only that side if you pick this tactic.</p>"
                            ,
                        },
                        {
                            "node": findTacticByName(pt.curNode.children, "right"),
                            "arrowPosition": "top",
                            "contents":
                            "<p>The <code>right</code> tactic should be used when you think the right side of a disjunction is true.</p>"
                            ,
                        },
                        {
                            "node": findTacticByName(pt.curNode.children, "destruct b"),
                            "arrowPosition": "top",
                            "contents":
                            "<p>The <code>destruct</code> tactic lets you perform case-analysis on a value, according to its type. Here, it will split your goal into two subgoals, one for the case where <code>b</code> is <code>true</code>, and one for the case where <code>b</code> is <code>false</code>.</p>"
                            ,
                        },
                    ]);
                }
                return;
                break;

            };

            if (pt.curNode.allChildren.length === 0) {
                tooltipSequence(pt, [
                    {
                        "node": pt.curNode,
                        "arrowPosition": "top",
                        "contents":
                        "<p>No tactic applies to this goal!</p>"
                            + "<p>We can't solve it, it might be false!</p>"
                        ,
                    },
                    {
                        "node": pt.curNode.parent,
                        "arrowPosition": "top",
                        "contents":
                        "<p>Looks like you made a wrong decision.</p>"
                            + "<p>Click on this node to go back.</p>"
                        ,
                    },
                ]);
                return;
            }

            if (!pt.userState.introducedFinishingTactic
                && pt.curNode.allChildren.length === 1
                && pt.curNode.allChildren[0].allChildren.length === 0) {
                pt.userState.introducedFinishingTactic = true;
                tooltipSequence(pt, [
                    {
                        "node": pt.curNode.allChildren[0],
                        "arrowPosition": "right",
                        "contents":
                        "<p><code>reflexivity</code> does not have any subgoal.</p>"
                            + "<p>This means it solves the subgoal!</p>"
                            + "<p><code>reflexivity</code> can solve any equality where the two sides have the same value.</p>"
                            + "<p>Once you click on it, an animation will fold the "
                            + "things that have been proven.</p>"
                        ,
                    },
                ]);
                return;
            }

        }
    ));

    add(mkText(
        "<p>Once you are done with the proof, you should see the outline of the proof you just build. The Coq Proof Assistant registered the proof under the name <code>bools_are_true_or_false</code>.</p><p>The <code>Check</code> command lets you see the type of any value.</p>"
    ));

    add(mkCoqReadonly(
        "Check bools_are_true_or_false."
    ));

    add(mkText(
        "<p>Let's define a function which returns the boolean disjunction of its input: the output is <code>true</code> if either of the two arguments is <code>true</code>.</p>"
    ));

    add(mkCoqReadonly(
        "Definition orb (a b : bool) : bool :=\n"
            + "  match a, b with\n"
            + "  | false, false => false\n"
            + "  | _, _ => true\n"
            + "  end."
    ));

    add(mkText(
        "<p>Now try to prove that <code>orb true b</code> is always <code>true</code> regardless of <code>b</code>.</p>"
    ));

    add(mkCoqReadonly(
        "Theorem orb_true_left : forall b, orb true b = true.",
        function(pt) {
            if (pt.curNode.depth == 0) {
                return ["intro"];
            } else {
                return ["reflexivity"];
            }
        }
    ));

    add(mkText(
        "<p>Now we will work with natural numbers. They are defined in Coq as yet another inductive type, but this one is recursive: a number is either <code>O</code> for zero, or the successor of a number (that is, the next one), noted <code>S n</code> where <code>n</code> is the predecessor.</p>"
    ));

    add(mkCoqReadonly(
        "Inductive nat : Type :=\n"
            + "| O : nat\n"
            + "| S : nat -> nat\n"
            + "."
    ));

    add(mkText(
        "<p>This encoding of natural numbers is called the Peano encoding. If you've never seen it before, here are a few constants.</p>"
    ));

    add(mkCoqReadonly(
        "Check O. (* zero *)"
    ));

    add(mkCoqReadonly(
        "Check (S (S O)). (* two *)"
    ));

}
