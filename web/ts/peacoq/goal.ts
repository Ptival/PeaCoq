import * as Coq85 from "../editor/coq85";
import { htmlPrintConstrExpr, htmlPrintHyps } from "../printing/html-printers";

export default PeaCoqGoal;

// TODO: maybe add a mechanism to cache different renderings based on
// some settings, for instance, whether to show diff, whether to merge
// multiple lines with same variables
// This might be complicated in collaboration with other features like
// printing diffs between lines, as merging messes with this...

export class PeaCoqGoal implements IPeaCoqGoal {
  private html: JQuery | null;

  constructor(
    public hyps: PeaCoqHyp[],
    public concl: IConstrExpr
  ) {
    this.html = null; // rendered on-demand and cached
  }

  getHTML(): JQuery {
    if (this.html === null) {
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
        if (Coq85.sameBodyAndType(elt, prevElt)) {
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

function makeContextDivider() {
  return $("<hr>", { class: "context-divider" });
}
