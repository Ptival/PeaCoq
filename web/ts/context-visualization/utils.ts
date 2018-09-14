import * as _ from 'lodash'
import { Maybe } from 'tsmonad'

import * as Pp from '../coq/lib/pp'
import * as PpExtend from '../coq/interp/ppextend'
import * as Pattern from './pattern'
import { StrDef } from '../coq/str-token'
import * as PeaCoqUtils from '../peacoq/utils'

export function findPpCmdSuchThat(
    l : Pp.t[],
    predicate : (_1 : Pp.t) => boolean
) : number {
    return _.findIndex(l, predicate)
}

export function ppCmdIsStringSuchThat(
    predicate : (_1 : string) => boolean
) : (_1 : Pp.t) => boolean {
    return (token : Pp.t) => {
        if (token instanceof Pp.PpCmdString) {
            return predicate(token.str)
        }
        return false
    }
}

export function ppCmdIsString(s : string) : (_1 : Pp.t) => boolean {
    return ppCmdIsStringSuchThat((s1) => s === s1.trim())
}

export function replacePpCmd(
    match : (_1 : Pp.t) => boolean,
    replace : (_1 : Pp.t) => Pp.t[],
    l : Pp.t[]
) : Pp.t[] {
    const pos = findPpCmdSuchThat(l, match)
    if (pos < 0) { return l }
    return ([] as Pp.t[]).concat(
        l.slice(0, pos),
        replace(l[pos]),
        l.slice(pos + 1)
    )
}

/*
  In practice the tokens come with their spacing incorporated, which is
  sometimes \u00A0<token> or sometimes <token>\u00A0, so we perform the
  replacement with a regexp to preserve the \u00A0.
*/
export function replaceToken(s1 : string, s2 : string, l : Pp.t[]) : Pp.t[] {
    return replacePpCmd(
        ppCmdIsString(s1),
        (t : Pp.t) => {
            if (!(t instanceof Pp.PpCmdString)) { throw t }
            return [Pp.str(t.str.replace(s1, s2))]
        },
        l
    )
}

function ppCmdsMatchGen(p : Pattern.Pattern[], l : Pp.t[], o : Object) : Maybe<Object> {
    if (p.length !== l.length) { return Maybe.nothing() }
    const zip = _.zip(p, l)
    for (const index in zip) {
        const [pat, cmd] = zip[index]
        if (!pat) { return Maybe.nothing() }
        const shortCircuit = ppCmdMatchGen(pat, cmd, o).caseOf({
            nothing : () => true,
            just : (newo) => {
                o = newo
                return false
            }
        })
        if (shortCircuit) { return Maybe.nothing() }
    }
    return Maybe.just(o)
}

function reduceMaybe<IN, ACC>(
    a : Array<IN>,
    f : (_1 : ACC, _2 : IN) => Maybe<ACC>,
    acc : ACC
) : Maybe<ACC> {
    return _.reduce(
        a,
        (acc : Maybe<ACC>, elt : IN) => {
            return acc.caseOf({
                nothing : () => acc,
                just : (acc) => f(acc, elt),
            })
        },
        Maybe.just(acc)
    )
}

function ppCmdMatchGen(pat : Pattern.Pattern, p : Pp.t | any, o : Object) : Maybe<Object> {
    if (pat instanceof Pattern.Anything) {
        return Maybe.just(o)
    } else if (pat instanceof Pattern.ArrayPattern) {
        if (!(p instanceof Array)) { throw PeaCoqUtils.MatchFailure('ppCmdMatchGen > ArrayPattern', p) }
        return ppCmdsMatchGen(pat.array, p, o)
    } else if (pat instanceof Pattern.BinderPattern) {
        const binder = pat.binder
        o[binder] = p
        return Maybe.just(o)
    } else if (pat instanceof Pattern.Constructor) {
        if (p instanceof pat.name) {
            return reduceMaybe(
                Object.keys(pat.fields),
                (acc, field) => {
                    if (field in p) {
                        return ppCmdMatchGen((<Pattern.Constructor>pat).fields[field], p[field], acc)
                    } else {
                        return Maybe.nothing()
                    }
                },
                o
            )
        } else {
            return Maybe.nothing()
        }
    } else if (pat instanceof Pattern.StringPattern) {
        if (!(typeof p === 'string')) {
            throw PeaCoqUtils.MatchFailure('ppCmdMatchGen > StringPattern', p)
        }
        if (pat.str === p) {
            return Maybe.just(o)
        } else {
            return Maybe.nothing()
        }
    } else {
        throw PeaCoqUtils.MatchFailure('patternMatch > rec', pat)
    }
}

function ppCmdsMatch(p : Pattern.Pattern[], l : Pp.t[]) : Maybe<Object> {
    return ppCmdsMatchGen(p, l, {})
}

export function matchPattern(
    l : Pp.t[],
    pat : Pattern.Pattern[],
    h : (_1 : any) => Pp.t[]
) : Pp.t[] {
    return ppCmdsMatch(pat, l).caseOf({
        nothing : () => l,
        just : (m) => h(m),
    })
}
