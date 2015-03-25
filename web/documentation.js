var documentation = {

    "admit": {
        "text": "Admits the current goal as proved.",
        "doc": ["10", "60"],
    },

    "constructor": {
        "text": "Tries to apply a constructor of the type of the goal.",
        "doc": ["10", "17"],
    },

    "destruct": {
        "text": "Performs case analysis on its argument, yielding one goal per constructor.",
        "doc": ["10", "65"],
    },

    "discriminate": {
        "text": "Proves any goal when your context contains an equality between two different constructors.",
        "doc": ["10", "82"],
    },

    "econstructor": {
        "text": "Tries to apply a constructor of the type of the goal. The 'e' prefix means this tactic may instantiate existential unification variables.",
        "doc": ["10", "22"],
    },

    "firstorder": {
        "text": "Solver for first-order logic.",
        "doc": ["10", "149"],
    },

    "induction": {
        "text": "Performs case analysis on its argument, yielding one goal per constructor, and adding induction hypotheses in your context for the inductive cases.",
        "doc": ["10", "71"],
    },

    "intro": {
        "text": "Introduces one variable from the goal into your context.",
        "doc": ["10", "27"],
    },

    "intros": {
        "text": "Introduces all the variables explicitly quantified in the current goal into your context.",
        "doc": ["10", "28"],
    },

    "inversion": {
        "text": "Performs case analysis on its argument, figuring out impossible cases, and retaining equations for the indices.",
        "doc": ["10", "87"],
    },

    "reflexivity": {
        "text": "Proves equality goals when the two sides are equal up to computation rules.",
        "doc": ["10", "118"],
    },

    "subst": {
        "text": "For all proofs that a variable is equal to something else in your context, replaces that variable with the other side of the equality everywhere possible.",
        "doc": ["10", "122"],
    },


};

function fillDocumentation(div, t) {
    if (documentation.hasOwnProperty(t)) {
        var doc = documentation[t];
        div
            .append(
                $("<span>").text(doc.text)
            )
            .append(
                $("<br/>")
            )
            .append(
                $("<a>")
                    .attr(
                        "href",
                        "https://coq.inria.fr/distrib/current/refman/Reference-Manual0"
                            + doc.doc[0]
                            + ".html#hevea_tactic"
                            + doc.doc[1]
                    )
                    .attr("target", "_blank")
                    .text("Link to documentation")
            )
        ;
    } else {
        div.text("Documentation unavailable");
    }
}
