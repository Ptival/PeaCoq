function DocItem(template, docHTML, section, number) {
    return {
        "template": template,
        "html": docHTML,
        "url": "https://coq.inria.fr/distrib/current/refman/Reference-Manual0"
            + section
            + ".html#hevea_tactic"
            + number,
    };
}

var applyDoc = [
    DocItem(
        "apply term",
        "If the conclusion of the type of term matches the goal, the term is used to prove the goal, and obligations are left to be proven for each argument of term that could not be inferred.",
        10, 8
    ),
    DocItem(
        "apply term in ident",
        "If the conclusion of the hypothesis ident matches an argument of term (testing from right to left), the hypothesis is replaced with the conclusion of term, and obligations are left for the other arguments of term that could not be inferred.",
        10, 13
    ),
    DocItem(
        "eapply term",
        "Same as apply, but introduces existential unification variables for terms it cannot infer.",
        10, 10
    ),
];

var constructorDoc = [
    DocItem(
        "constructor",
        "If your goal is an inductive type t, constructor tries to apply a constructor of that type.",
        10, 17
    ),
    DocItem(
        "econstructor",
        "Same as constructor, but introduces existential unification variables for terms it cannot infer.",
        10, 22
    ),
];

var documentation = {

    "admit": [
        DocItem(
            "admit",
            "Admits the current goal as proved.",
            10, 60
        ),
    ],

    "apply": applyDoc,

    "constructor": constructorDoc,

    "destruct": [
        DocItem(
            "destruct term",
            "Performs case analysis on its argument, yielding one goal per constructor.",
            10, 65
        ),
    ],

    "discriminate": [
        DocItem(
            "discriminate",
            "Proves any goal when your context contains an equality between two different constructors.",
            10, 82
        ),
    ],

    "eapply": applyDoc,

    "econstructor": constructorDoc,

    "firstorder": [
        DocItem(
            "firstorder",
            "Solver for first-order logic.",
            10, 149
        ),
    ],

    "induction": [
        DocItem(
            "induction term",
            "Performs case analysis on its argument, yielding one goal per constructor, and adding induction hypotheses in your context for the inductive cases.",
            10, 71
        ),
    ],

    "intro": [
        DocItem(
            "intro",
            "Introduces one variable from the goal into your context.",
            10, 27
        ),
    ],

    "intros": [
        DocItem(
            "intros",
            "Introduces all the variables explicitly quantified in the current goal into your context.",
            10, 28
        ),
    ],

    "inversion": [
        DocItem(
            "inversion ident",
            "Performs case analysis on its argument, figuring out impossible cases, and retaining equations for the indices.",
            10, 87
        ),
    ],

    "left": [
        DocItem(
            "left",
            "If your goal is an inductive type with two constructors, applies the first one. Typically used for proving the left side of a disjunction.",
            10, 20
        ),
    ],

    "reflexivity": [
        DocItem(
            "reflexivity",
            "Proves equality goals when the two sides are equal up to computation rules.",
            10, 118
        ),
    ],

    "remember": [
        DocItem(
            "remember term",
            "Introduces a new variable of the same type as the argument, and a proof that this new variable is equal to the argument. Useful when you want to apply a theorem but keep the original variable, or when you want to save equations across tactics that lose information like destruct and inversion.",
            10, 44
        ),
    ],

    "right": [
        DocItem(
            "right",
            "If your goal is an inductive type with two constructors, applies the second one. Typically used for proving the right side of a disjunction.",
            10, 21
        ),
    ],

    "subst": [
        DocItem(
            "subst",
            "For all proofs that a variable is equal to something else in your context, replaces that variable with the other side of the equality everywhere possible.",
            10, 122
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
            )
        ;
    });
    div.append(dl);
}
