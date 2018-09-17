import * as Pp from '../coq/lib/pp'

/*
  peaCoqBox should not disrupt the pretty-printing flow, but add a
  <span> so that sub-expression highlighting is more accurate
*/
export function peaCoqBox(l : Pp.T) : Pp.T {
    return new Pp.PpCmdBox(new Pp.PpHoVBox(0), l)
}
