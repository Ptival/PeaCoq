import * as ConstrExpr from '../coq/intf/constr-expr'
import { prConstrExpr } from '../coq/printing/ppconstr'
import { htmlPrintPpCmds, htmlPrintPpCmdsDiff } from '../context-visualization/printers'

export function htmlPrintConstrExpr(c : ConstrExpr.ConstrExpr) : string {
  const ppCmds = prConstrExpr(c)
  // console.log(ppCmds)
  return htmlPrintPpCmds([ppCmds])
}

export function htmlPrintConstrExprDiff(c : ConstrExpr.ConstrExpr, old : ConstrExpr.ConstrExpr) : string {
  const ppCmds = prConstrExpr(c)
  const oldPpCmds = prConstrExpr(old)
  console.log(ppCmds)
  // return htmlPrintPpCmds(ppCmds)
  return htmlPrintPpCmdsDiff([ppCmds], [oldPpCmds])
}

export function htmlPrintHyp(h : PeaCoqHyp) : string {
  let result = `<span><span class="tag-variable">${h.name}</span></span>`
  const maybeTerm = h.maybeTerm
  result += maybeTerm.caseOf({
    nothing : () => '',
    just : (t) => `<span>\u00A0 :=\u00A0</span><span>${htmlPrintConstrExpr(t)}</span>`,
  })
  result += `<span> :\u00A0</span><span>${htmlPrintConstrExpr(h.type)}</span>`
  return result
}

export function htmlPrintHyps(hyps : PeaCoqHyp[]) : string {
  return hyps.reduce(
    (acc, elt) => `${acc}<div class="hyp">${htmlPrintHyp(elt)}</div>`,
    ''
  )
}
