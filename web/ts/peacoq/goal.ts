import * as _ from 'lodash'

import { htmlPrintConstrExpr, htmlPrintHyps } from '../printing/html-printers'

// export default PeaCoqGoal

// TODO : maybe add a mechanism to cache different renderings based on
// some settings, for instance, whether to show diff, whether to merge
// multiple lines with same variables
// This might be complicated in collaboration with other features like
// printing diffs between lines, as merging messes with this...

export class PeaCoqGoal implements IPeaCoqGoal {
  private html : JQuery | null

  constructor(
    public hyps : PeaCoqHyp[],
    public concl : IConstrExpr
  ) {
    this.html = null // rendered on-demand and cached
  }

  public getHTML() : JQuery {
    if (this.html === null) {
      this.html = $('<div>')
      // TODO : htmlPrintHypsDiff
      const hypsDiv = $('<div>').html(htmlPrintHyps(this.hyps))
      this.html.append(hypsDiv)
      this.html.append(makeContextDivider())
      // TODO : htmlPrintConstrExprDiff
      this.html.append(
        $('<div>').html(htmlPrintConstrExpr(this.concl))
      )

      /*
        Now, let's merge redundant variables on a single line
          a : nat, b : nat
        becomes :
          a, b : nat
      */

      const hyps = hypsDiv.children('.hyp')
      // if the previous hyp has the same body/type, merge it in
      _.forEach(hyps, (elt, ndx) => {
        if (ndx === 0) { return }
        const prevElt = hyps[ndx - 1]
        if (sameBodyAndType(elt, prevElt)) {
          // prepend the names of the previous hyp, then delete previous
          const spanToPrependTo = $(elt).children('span')[0]
          const spanToPrependFrom = $(prevElt).children('span')[0]
          $(spanToPrependTo).html($(spanToPrependFrom).html() + ', ' + $(spanToPrependTo).html())
          $(prevElt).remove()
        }
      })

    }

    return this.html.clone()
  }
}

function makeContextDivider() {
  return $('<hr>', { class : 'context-divider' })
}

function sameBodyAndType(hyp1 : HTMLElement, hyp2 : HTMLElement) : boolean {
  const children1 = $(hyp1).children().slice(1)
  const children2 = $(hyp2).children().slice(1)
  if (children1.length !== children2.length) { return false }
  for (const i in _.range(children1.length)) {
    if ($(children1[i]).html() !== $(children2[i]).html()) {
      return false
    }
  }
  return true
}
