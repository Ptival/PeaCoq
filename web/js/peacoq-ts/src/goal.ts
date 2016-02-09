// TODO: maybe add a mechanism to cache different renderings based on
// some settings, for instance, whether to show diff, whether to merge
// multiple lines with same variables
// This might be complicated in collaboration with other features like
// printing diffs between lines, as merging messes with this...

class PeaCoqGoal {
  html: JQuery;
  hyps: PeaCoqHyp[];
  concl: ConstrExpr;

  constructor(hyps, concl) {
    this.html = undefined; // rendered on-demand and cached
    this.hyps = hyps;
    this.concl = concl;
  }

  getHTML(): JQuery {
    if (this.html === undefined) {
      this.html = $("<div>");
      // TODO: htmlPrintHypsDiff
      let hypsDiv = $("<div>").html(htmlPrintHyps(this.hyps));
      this.html.append(hypsDiv);
      this.html.append(makeContextDivider());
      // TODO: htmlPrintConstrExprDiff
      this.html.append(
        $("<div>").html(htmlPrintConstrExpr(this.concl))
      );

      /*
        Now, let's merge redundant variables on a single line
          a: nat, b: nat
        becomes:
          a, b: nat
      */

      let hyps = hypsDiv.children(".hyp");
      // if the previous hyp has the same body/type, merge it in
      _.forEach(hyps, function(elt, ndx) {
        if (ndx === 0) { return; }
        let prevElt = hyps[ndx - 1];
        if (sameBodyAndType(elt, prevElt)) {
          // prepend the names of the previous hyp, then delete previous
          let spanToPrependTo = $(elt).children("span")[0];
          let spanToPrependFrom = $(prevElt).children("span")[0];
          $(spanToPrependTo).html($(spanToPrependFrom).html() + ", " + $(spanToPrependTo).html());
          $(prevElt).remove();
        }
      });

    }
    return this.html.clone();
  }
}
