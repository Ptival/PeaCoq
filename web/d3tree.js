
var theorems = [
['Theorem branching : ∀(a b : comparison), a = Eq → b = Eq → a = b.', PT.tDestruct],
['Theorem plus_O_n : ∀n : nat, 0 + n = n.', PT.tIntro],
['Theorem plus_1_l : ∀n : nat, 1 + n = S n.', PT.tIntro],
['Theorem mult_0_l : ∀n : nat, 0 * n = 0.', PT.tIntro],
['Theorem plus_id_example : ∀n m:nat, n = m → n + n = m + m.', PT.tRewrite],
['Theorem plus_id_exercise : ∀n m o : nat, n = m → m = o → n + m = m + o.', PT.tRewrite],
['Theorem mult_0_plus : ∀n m : nat, (0 + n) * m = n * m.', PT.tRewrite],
['Theorem mult_S_1 : ∀n m : nat, m = S n → m * (1 + n) = m * m.', PT.tRewrite],
['Theorem negb_involutive : ∀b : bool, negb (negb b) = b.', PT.tDestruct],
['Theorem identity_fn_applied_twice : ∀(f : bool → bool), (∀(x : bool), f x = x) → ∀(b : bool), f (f b) = b.',
 PT.tDestruct],
['Theorem andb_eq_orb : ∀(b c : bool), (andb b c = orb b c) → b = c.',
 PT.tDestruct.concat(['admit'])],
['Theorem andb_true_elim1 : ∀b c : bool, andb b c = true → b = true.', PT.tDestruct],
['Theorem andb_true_elim2 : ∀b c : bool, andb b c = true → c = true.', PT.tDestruct],
['Theorem plus_0_r : ∀n:nat, n + 0 = n.', PT.tInduction],
['Theorem minus_diag : ∀n, minus n n = 0.', PT.tInduction],
['Theorem mult_0_r : ∀n:nat, n * 0 = 0.', PT.tInduction],
['Theorem plus_n_Sm : ∀n m : nat, S (n + m) = n + (S m).', PT.tInduction],
['Theorem plus_comm : ∀n m : nat, n + m = m + n.', PT.tInduction],
['Theorem plus_assoc : ∀n m p : nat, n + (m + p) = (n + m) + p.', PT.tInduction],
['Theorem plus_rearrange : ∀n m p q : nat, (n + m) + (p + q) = (m + n) + (p + q).',
 PT.tInduction],
['Theorem plus_swap : ∀n m p : nat, n + (m + p) = m + (n + p).', PT.tInduction],
['Theorem mult_comm : ∀m n : nat, m * n = n * m.', PT.tInduction],
['Theorem andb_false_r : ∀b : bool, andb b false = false.', PT.tInduction],
['Theorem mult_1_l : ∀n:nat, 1 * n = n.', PT.tInduction],
['Theorem all3_spec : ∀b c : bool, orb (andb b c) (orb (negb b) (negb c)) = true.',
 PT.tInduction],
['Theorem mult_plus_distr_r : ∀n m p : nat, (n + m) * p = (n * p) + (m * p).', PT.tInduction],
['Theorem mult_assoc : ∀n m p : nat, n * (m * p) = (n * m) * p.', PT.tInduction],
];

function qed(prooftree) {
    prooftree.svg
        .style("display", "none")
    ;
    prooftree.proof
        .style("display", "")
        .html(
            "Require Import Unicode.Utf8.<br><br>"
                + prooftree.theorem
                + "<br>Proof.<br>"
                + PT.pprint(PT.proof(prooftree.rootNode), 1)
                + "Qed."
        )
    ;
}

$(document).ready(function() {

    PT.handleKeyboard();

    var ndx = 0;

    var scrollbarWidth = 20; // arbitrary

    _(theorems).each(_.partial(addTheorem, pt));

    $("body").prepend($("<div>").attr("id", "pt"))

    var pt = new ProofTree(
        d3.select("#pt"),
        $(window).width() - scrollbarWidth,
        $(window).height() - $("#tips").height() - $("#buttons").height(),
        qed
    );

    $(".theorem")
        .click(function() {
            var t = $(this).data("theorem");
            pt.syncQuery("Abort All.", hIgnore);
            pt.newTheorem(t[0], t[1], function() { }, clickRoot);
        })
    ;

    makeActive(pt);

    var verbose =
        true
        //false
    ;
    if (verbose) {
        pt.syncRequest("unsetprintingall", "", function() {});
    } else {
        pt.syncRequest("setprintingall", "", function() {});
    }

    pt.syncQuery("Abort All.", hIgnore);
    pt.newTheorem(
        theorems[ndx][0],
        theorems[ndx][1],
        function() { },
        clickRoot
    );

});

function clickRoot(pt) {
    pt.click(pt.rootNode);
}

function addTheorem(pt, t, ndx) {
    var b = $('<button>')
        .addClass("theorem")
        .text(t[0])
        .data("theorem", t)
    ;
    $('#buttons').append(b);
}
