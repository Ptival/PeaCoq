
var theorems = [
['Theorem branching : ∀(a b : comparison), a = Eq → b = Eq → a = b.', tDestruct],
['Theorem plus_O_n : ∀n : nat, 0 + n = n.', tIntro],
['Theorem plus_1_l : ∀n : nat, 1 + n = S n.', tIntro],
['Theorem mult_0_l : ∀n : nat, 0 * n = 0.', tIntro],
['Theorem plus_id_example : ∀n m:nat, n = m → n + n = m + m.', tRewrite],
['Theorem plus_id_exercise : ∀n m o : nat, n = m → m = o → n + m = m + o.', tRewrite],
['Theorem mult_0_plus : ∀n m : nat, (0 + n) * m = n * m.', tRewrite],
['Theorem mult_S_1 : ∀n m : nat, m = S n → m * (1 + n) = m * m.', tRewrite],
['Theorem negb_involutive : ∀b : bool, negb (negb b) = b.', tDestruct],
['Theorem identity_fn_applied_twice : ∀(f : bool → bool), (∀(x : bool), f x = x) → ∀(b : bool), f (f b) = b.', tDestruct],
['Theorem andb_eq_orb : ∀(b c : bool), (andb b c = orb b c) → b = c.', tDestruct.concat(['admit'])],
['Theorem andb_true_elim1 : ∀b c : bool, andb b c = true → b = true.', tDestruct],
['Theorem andb_true_elim2 : ∀b c : bool, andb b c = true → c = true.', tDestruct],
['Theorem plus_0_r : ∀n:nat, n + 0 = n.', tInduction],
['Theorem minus_diag : ∀n, minus n n = 0.', tInduction],
['Theorem mult_0_r : ∀n:nat, n * 0 = 0.', tInduction],
['Theorem plus_n_Sm : ∀n m : nat, S (n + m) = n + (S m).', tInduction],
['Theorem plus_comm : ∀n m : nat, n + m = m + n.', tInduction],
['Theorem plus_assoc : ∀n m p : nat, n + (m + p) = (n + m) + p.', tInduction],
['Theorem plus_rearrange : ∀n m p q : nat, (n + m) + (p + q) = (m + n) + (p + q).', tInduction],
['Theorem plus_swap : ∀n m p : nat, n + (m + p) = m + (n + p).', tInduction],
['Theorem mult_comm : ∀m n : nat, m * n = n * m.', tInduction],
['Theorem andb_false_r : ∀b : bool, andb b false = false.', tInduction],
['Theorem mult_1_l : ∀n:nat, 1 * n = n.', tInduction],
['Theorem all3_spec : ∀b c : bool, orb (andb b c) (orb (negb b) (negb c)) = true.', tInduction],
['Theorem mult_plus_distr_r : ∀n m p : nat, (n + m) * p = (n * p) + (m * p).', tInduction],
['Theorem mult_assoc : ∀n m p : nat, n * (m * p) = (n * m) * p.', tInduction],
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
                + pprint(proof(prooftree.rootNode), 1)
                + "Qed."
        )
    ;
}

$(document).ready(function() {

    _(theorems).each(addTheorem);

    var ndx = 0;

    var scrollbarWidth = 20; // arbitrary

    $("body").prepend($("<div>").attr("id", "pt1"));
    $("body").prepend($("<div>").attr("id", "pt2"));

    var pt = new ProofTree(
        d3.select("#pt1"),
        $(window).width() - scrollbarWidth,
        $(window).height() - $("#tips").height() - $("#buttons").height(),
        qed
    );

    makeActive(pt);

    pt.newTheorem(
        theorems[ndx][0],
        theorems[ndx][1],
        clickRoot
    );

/*
    var pt2 = new ProofTree(
        d3.select("#pt2"),
        $(window).width() - scrollbarWidth,
        $(window).height()/2,
        qed
    );

    pt2.newTheorem(
        theorems[ndx+1][0],
        theorems[ndx+1][1]
    );
*/

});

function clickRoot() {
    activeProofTree.click(activeProofTree.rootNode);
}

function addTheorem(t, ndx) {
    var b = $('<button>', {
        text: t[0],
        click: function() {
            activeProofTree.newTheorem(t[0], t[1], clickRoot);
        }
    });
    $('#buttons').append(b);
}
