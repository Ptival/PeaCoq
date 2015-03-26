function DocItem(template, docHTML, section, number, mirrorNumber) {
    return {
        "template": template,
        "html": docHTML,
        "url":
        "https://coq.inria.fr/distrib/current/refman/Reference-Manual0"
            + section
            + ".html#hevea_tactic"
            + number,
        "mirror":
        "http://flint.cs.yale.edu/cs428/coq/doc/Reference-Manual0"
            + section
            + ".html#@tactic"
            + mirrorNumber,
    };
}

var applyDoc = [
    DocItem(
        "apply <i>t</i>",
        "If the conclusion of <i>t</i>'s type of term matches the goal, <i>t</i> is used to prove the goal, and obligations are left to be proven for each argument of <i>t<i> that could not be inferred.",
        10, 8, 16
    ),
    DocItem(
        "apply <i>t</i> in <i>H</i>",
        "If the conclusion of the hypothesis ident matches an argument of term (testing from right to left), the hypothesis is replaced with the conclusion of term, and obligations are left for the other arguments of term that could not be inferred.",
        10, 13, 16
    ),
    DocItem(
        "eapply <i>t</i>",
        "Same as apply, but introduces existential unification variables for terms it cannot infer.",
        10, 10, 18
    ),
];

var assumptionDoc = [
    DocItem(
        "assumption",
        "Solves a goal if a hypothesis has the exact type.",
        10, 5, 5
    ),
    DocItem(
        "eassumption",
        "Same as assumption, but also works if your goal has existential unification variables.",
        10, 6, 5
    ),
];

var autoDoc = [
    DocItem(
        "auto",
        "Automation procedure that attemps to solve your goal using a resolution procedure and the hints provided by the user.",
        10, 141, 108
    ),
    DocItem(
        "auto 6",
        "Same as auto, but searches to a depth of 6 (the default being 5).",
        10, 141, 108
    ),
    DocItem(
        "eauto",
        "eauto is like auto, but it uses eapply instead of apply. As a result, it may create intermediate existential unification variables.",
        10, 143, 110
    ),
];

var constructorDoc = [
    DocItem(
        "constructor",
        "If your goal is an inductive type t, constructor tries to apply a constructor of that type.",
        10, 17, 42
    ),
    DocItem(
        "econstructor",
        "Same as constructor, but introduces existential unification variables for terms it cannot infer.",
        10, 22, 42
    ),
];

var rewriteDoc = [
    DocItem(
        "rewrite <i>H</i>",
        "Assuming <i>H</i> has type <code>t1 = t2</code>, replaces occurences of <i>t1</i> with <i>t2</i> in the goal.",
        10, 109, 63
    ),
    DocItem(
        "rewrite -> <i>H</i>",
        "Same as rewrite H.",
        10, 110, 64
    ),
    DocItem(
        "rewrite <- <i>H</i>",
        "Same as <code>rewrite H</code>, but replaces occurences of <i>t2</i> with <i>t1</i>.",
        10, 111, 65
    ),
    DocItem(
        "rewrite <i>H1</i> in <i>H2</i>",
        "Same as <code>rewrite H1</code>, but replaces occurences in hypothesis <i>H2</i> rather than the goal.",
        10, 112, 66
    ),
];

var documentation = {

    "admit": [
        DocItem(
            "admit",
            "Admits the current goal as proved.",
            10, 60, 0
        ),
    ],

    "apply": applyDoc,

    "auto": autoDoc,

    "congruence": [
        DocItem(
            "congruence",
            "Proves equality goals when the two sides are equal and goals where the equalities in the context are contradictory.",
            10, 153, 117
        ),
    ],

    "constructor": constructorDoc,

    "destruct": [
        DocItem(
            "destruct <i>t</i>",
            "Performs case analysis <i>t</i>, yielding one goal per constructor of its type, where <i>t</i> is replaced by its constructor, with fresh arguments introduced in the context (if any).",
            10, 65, 53
        ),
    ],

    "discriminate": [
        DocItem(
            "discriminate",
            "Proves any goal when your context contains an equality between two different constructors.",
            10, 82, 80
        ),
    ],

    "eapply": applyDoc,

    "eauto": autoDoc,

    "econstructor": constructorDoc,

    "firstorder": [
        DocItem(
            "firstorder",
            "Solver for first-order logic.",
            10, 149, 113
        ),
    ],

    "induction": [
        DocItem(
            "induction <i>t</i>",
            "Performs case analysis <i>t</i>, yielding one goal per constructor of its type, and adding induction hypotheses in your context for the inductive cases.",
            10, 71, 48
        ),
    ],

    "intro": [
        DocItem(
            "intro",
            "Introduces one variable from the goal into your context.",
            10, 27, 10
        ),
    ],

    "intros": [
        DocItem(
            "intros",
            "Introduces all the variables explicitly quantified in the current goal into your context.",
            10, 28, 11
        ),
    ],

    "inversion": [
        DocItem(
            "inversion <i>t</i>",
            "Performs case analysis on <i>t</i>, figuring out impossible cases, and retaining equations for the indices.",
            10, 87, 87
        ),
    ],

    "left": [
        DocItem(
            "left",
            "If your goal is an inductive type with two constructors, applies the first one. Typically used for proving the left side of a disjunction.",
            10, 20, 46
        ),
    ],

    "reflexivity": [
        DocItem(
            "reflexivity",
            "Proves equality goals when the two sides are equal up to computation rules.",
            10, 118, 71
        ),
    ],

    "remember": [
        DocItem(
            "remember <i>foo</i>",
            "Introduces a new variable <i>foo'</i>of the same type as the term <i>foo</i>, and a proof <i>H</i> that <i>foo'</i> is equal to <i>foo</i>. Useful when you want to apply a theorem but keep the original variable, or when you want to save equations across tactics that lose information like destruct and inversion.",
            10, 44, 0
        ),
    ],

    "rewrite": rewriteDoc,

    "right": [
        DocItem(
            "right",
            "If your goal is an inductive type with two constructors, applies the second one. Typically used for proving the right side of a disjunction.",
            10, 21, 47
        ),
    ],

    "simpl": [
        DocItem(
            "simpl",
            "Simplifies the goal.",
            10, 135, 36
        ),
        DocItem(
            "simpl in <i>H</i>",
            "Simplifies the hypothesis <i>H</i>.",
            10, 136, 37
        ),
    ],

    "subst": [
        DocItem(
            "subst",
            "For all proofs that a variable is equal to something else in your context, replaces that variable with the other side of the equality everywhere possible.",
            10, 122, 75
        ),
    ],

    "unfold": [
        DocItem(
            "unfold <i>t</i>",
            "Replaces occurences of <i>t</i> in your goal with the body of the definition of <i>t</i>.",
            10, 138, 38
        ),
        DocItem(
            "unfold <i>t</i> in <i>H</i>",
            "Same as unfold, but replaces occurences in the hypothesis <i>H</i> rather than the goal.",
            10, 138, 39
        ),
    ],

};

function fillDocumentation(div, t) {
    if (!documentation.hasOwnProperty(t)) {
        div.text("Documentation unavailable");
        return;
    }
    var dl = $("<dl>");
    _(documentation[t]).each(function(item) {
        dl
            .append(
                $("<dt>").html(item.template)
            )
            .append(
                $("<dd>")
                    .html(item.html)
                    .append(" [")
                    .append(
                        $("<a>")
                            .attr("href", item.url)
                            .attr("target", "_blank")
                            .text("doc")
                    )
                    .append("]")
                    .append(" [")
                    .append(
                        $("<a>")
                            .attr("href", item.mirror)
                            .attr("target", "_blank")
                            .text("mirror")
                    )
                    .append("]")
            )
        ;
    });
    div.append(dl);
}
