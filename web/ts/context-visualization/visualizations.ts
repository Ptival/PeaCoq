import * as Pp from '../coq/lib/pp'
import * as PpExtend from '../coq/interp/ppextend'
import * as Pattern from './pattern'
import { StrDef } from '../coq/str-token'
import { findPpCmdSuchThat, matchPattern, ppCmdIsString, ppCmdIsStringSuchThat, replacePpCmd, replaceToken } from './utils'

const anyPattern = new Pattern.Anything()

function patternScopeDelimiters(l : Pp.T[]) : Pp.T[] {
    return replacePpCmd(
        ppCmdIsStringSuchThat(s => s.startsWith('%')),
        t => ([] as Pp.T[]).concat(
            Pp.str(`<span style="vertical-align: sub; color: #9C27B0; font-size: xx-small;">`),
            Pp.str((<any>t).token.string.replace('%', '')),
            Pp.str(`</span>`)
        ),
        l
    )
}

function patternForall(l : Pp.T[]) : Pp.T[] {
    return replaceToken('forall', '∀', l)
}

function patternExists(l : Pp.T[]) : Pp.T[] {
    return replaceToken('exists', '∃', l)
}

function patternArrow(l : Pp.T[]) : Pp.T[] {
    return replaceToken('->', '→', l)
}

function patternMult(l : Pp.T[]) : Pp.T[] {
    return replaceToken('*', '×', l)
}

function patternAnd(l : Pp.T[]) : Pp.T[] {
    return replaceToken('/\\', '∧', l)
}

function patternOr(l : Pp.T[]) : Pp.T[] {
    return replaceToken('\\/', '∨', l)
}

function patternEquiv(l : Pp.T[]) : Pp.T[] {
    return replaceToken('<->', '⇔', l)
}

function patternNat(l : Pp.T[]) : Pp.T[] {
    return replaceToken('nat', '\u2115', l)
}

function patternZ(l : Pp.T[]) : Pp.T[] {
    return replaceToken('Z', '\u2124', l)
}

function patternAbs(l : Pp.T[]) : Pp.T[] {
    return matchPattern(
        l,
        [
            box([
                box([
                    anyPattern, tok('Z'), anyPattern, tok('.'), anyPattern, tok('abs')
                ])
            ]),
            anyPattern,
            anyPattern
        ],
        match => {
            return ([] as Pp.T[]).concat(
                Pp.str('|'),
                l[2],
                Pp.str('|')
            )
        }
    )
}

/* Visualization for: x ^ y
   ...
   OpenTag('notation')
   '^ '
   CloseTag
   ...
*/
function patternPow(l : Pp.T[]) : Pp.T[] {
    const pos = findPpCmdSuchThat(l, ppCmdIsString('^'))
    if (pos > 0) {
        return ([] as Pp.T[]).concat(
            l.slice(0, pos - 2),
            Pp.str(`<span style='vertical-align: super;'>`),
            l.slice(pos + 2),
            Pp.str(`</span>`)
        )
    }
    return l
}

// for 'divides': \u2223
// for 'does not divide': \u2224
function patternDivides(l : Pp.T[]) : Pp.T[] {
    return matchPattern(
        l,
        [
            box([box([anyPattern, tok('divides'), anyPattern])]),
            anyPattern, anyPattern, anyPattern, anyPattern
        ],
        match => {
            return ([] as Pp.T[]).concat(
                [l[2]],
                [l[1]], // space
                Pp.str('\u2223'),
                [l[3]], // space
                [boxDropParentheses(l[4])]
            )
        }
    )
}

function patternZSquare(l : Pp.T[]) : Pp.T[] {
    return matchPattern(l,
                        [
        box([
            box([
                anyPattern, tok('Z'), anyPattern, tok('.'), anyPattern, tok('square'), anyPattern
            ])
        ]),
        anyPattern, anyPattern
    ],
                        match => {
                            return ([] as Pp.T[]).concat(
                                [l[2]],
                                Pp.str('²')
                            )
                        }
                       )
}

const anything : any = undefined

function box(contents : Pattern.Pattern[]) : Pattern.Pattern {
    return new Pattern.Constructor(Pp.PpCmdBox, { contents : new Pattern.ArrayPattern(contents) })
}

function tok(s : string) : Pattern.Pattern {
    return new Pattern.Constructor(Pp.PpCmdString, {
        token : new Pattern.Constructor(StrDef, { string : new Pattern.StringPattern(s) })
    })
}

function patternZOfNat(l : Pp.T[]) : Pp.T[] {
    return matchPattern(l,
                        // TODO: we could have a pattern like this one removing outer parentheses
                        [
        box([
            box([anyPattern, tok('Z'), anyPattern, anyPattern, anyPattern, tok('of_nat'), anyPattern])
        ]),
        anyPattern,
        anyPattern
    ],
                        match => {
                            return ([] as Pp.T[]).concat(
                                [l[2]],
                                Pp.str(`<span style="vertical-align: sub; font-size: xx-small;">`),
                                Pp.str('\u2115'),
                                Pp.str(`</span>`)
                            )
                        }
                       )
}

function boxDropParentheses(p : Pp.T) : Pp.T {
    debugger // FIXME
    // I think now it will look like a box with a glue of length 3 inside
    if (p instanceof Pp.PpCmdBox) { // && p.contents.length === 3) {
        const open = p.contents[0]
        const close = p.contents[2]
        if (open instanceof Pp.PpCmdString && open.str === '('
            && close instanceof Pp.PpCmdString && close.str === ')') {
            return p.contents[1]
        }
    }
    return p
}

function patternSumLambda(l : Pp.T[]) : Pp.T[] {
    return matchPattern(
        l,
        [
            box([box([anyPattern, tok('sum'), anyPattern])]),
            anyPattern,
            box([
                tok('('),
                box([box([
                    box([
                        anyPattern,
                        tok('fun'),
                        anyPattern,
                        anyPattern,
                        box([
                            box([new Pattern.BinderPattern('binder')]), // Binder binder
                            anyPattern, // tok('\u00A0:'),
                            anyPattern,
                            box([new Pattern.BinderPattern('type')]) // Binder type
                        ])
                    ]),
                    anyPattern,
                    anyPattern,
                    anyPattern,
                    new Pattern.BinderPattern('body') // Binder body
                ])]),
                tok(')')
            ]),
            anyPattern,
            new Pattern.BinderPattern('upperBound')
        ],
        match => {
            return ([] as Pp.T[]).concat(
                Pp.str(`<span style="display: flex; flex-flow: row; align-items: center;">`),
                Pp.str(`<span style="font-family: MathJax_Size4; font-size:120%;">(</span>`),
                Pp.str(`<span style="display: flex; flex-flow: column; margin-right: 0.5em;">`),
                Pp.str(`<span style="display: flex; flex-flow: row; justify-content: center;">`),
                Pp.str(`<span>`),
                boxDropParentheses(match.upperBound),
                Pp.str(`</span></span>`),
                Pp.str(`<span style="display:flex; flex-flow: row; justify-content: center; font-family: MathJax_Size2; font-size: 120%;">∑</span>`),
                Pp.str(`<span style="display: flex; flex-flow: row; justify-content: center;">`),
                Pp.str(`<span>`),
                match.binder,
                Pp.str(` = 0`),
                Pp.str(`</span></span></span>`),
                Pp.str(`<span><span>`),
                match.body,
                Pp.str(`</span>`),
                Pp.str(`</span><span style="font-family: MathJax_Size4; font-size:120%;">)</span></span>`)
            )
        }
    )
}

function patternSum(l : Pp.T[]) : Pp.T[] {
    return matchPattern(
        l,
        [
            box([box([anyPattern, tok('sum'), anyPattern])]),
            anyPattern,
            new Pattern.BinderPattern('summand'),
            anyPattern,
            new Pattern.BinderPattern('upperBound')
        ],
        match => {
            return ([] as Pp.T[]).concat(
                Pp.str(`<span style="display: flex; flex-flow: row; align-items: center;">`),
                Pp.str(`<span style="font-family: MathJax_Size4; font-size:120%;">(</span>`),
                Pp.str(`<span style="display: flex; flex-flow: column; margin-right: 0.5em;">`),
                Pp.str(`<span style="display: flex; flex-flow: row; justify-content: center;">`),
                Pp.str(`<span>`),
                boxDropParentheses(match.upperBound),
                Pp.str(`</span></span>`),
                Pp.str(`<span style="display:flex; flex-flow: row; justify-content: center; font-family: MathJax_Size2; font-size: 120%;">∑</span>`),
                Pp.str(`<span style="display: flex; flex-flow: row; justify-content: center;">`),
                Pp.str(`<span>0</span></span></span>`),
                Pp.str(`<span><span>`),
                match.summand,
                Pp.str(`</span>`),
                Pp.str(`</span><span style="font-family: MathJax_Size4; font-size:120%;">)</span></span>`)
            )
        }
    )
}

export const patterns : Array<(_1 : Pp.T[]) => Pp.T[]> = [
    patternPow,
    patternForall,
    patternExists,
    patternArrow,
    patternMult,
    patternScopeDelimiters,
    patternAnd,
    patternOr,
    patternEquiv,
    patternDivides,
    patternAbs,
    patternZSquare,
    patternZOfNat,
    patternSumLambda,
    patternSum, // keep this one after patternSumLambda as it is less general
    patternNat,
    patternZ,
]
