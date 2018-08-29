import * as _ from 'lodash'

import * as Pp from '../coq/lib/pp'
import * as PpExtend from '../coq/interp/ppextend'
import * as StrToken from '../coq/str-token'
import { patterns } from './visualizations'

function htmlPrintStrToken(t : StrToken.StrToken) : string {
    if (t instanceof StrToken.StrDef) {
        return (t.str)
    }
    if (t instanceof StrToken.StrLen) {
        return (t.str)
    }
    throw MatchFailure('htmlPrintStrToken', t)
}

function markDifferent(s : string) : string {
    return `<span class='syntax peacoq-diff'>${s}</span>`
}

function syntax(s : string) : string { return `<span class='syntax'>${s}</span>` }

function htmlPrintPpCmdDiff(p : Pp.t, old : Pp.t) : string {
    if (p.constructor !== old.constructor) {
        return markDifferent(htmlPrintPpCmd(p))
    }
    // if (p instanceof Pp.PpCmdPrint && old instanceof Pp.PpCmdPrint) {
    //   let res = htmlPrintStrToken(p.token)
    //   if (p.token.string !== old.token.string) { res = markDifferent(res) }
    //   return res
    // }
    if (p instanceof Pp.PpCmdBox && old instanceof Pp.PpCmdBox) {
        // FIXME: use blockType
        return syntax(htmlPrintPpCmdDiff(p.contents, old.contents))
    }
    if (p instanceof Pp.PpCmdPrintBreak) {
        return ' '.repeat(p.nspaces)
    }
    if (p instanceof Pp.PpCmdForceNewline) {
        return 'TODO: PpCmdForceNewline'
    }
    if (p instanceof Pp.PpCmdComment) {
        return 'TODO: PpCmdComment'
    }
    throw MatchFailure('htmlPrintPpCmd', p)
}

function box<T>(p : Pp.t, s : string) : string {
    return `<span class='box syntax'>${s}</span>`
}

export function htmlPrintPpCmd(p : Pp.t) : string {
    if (p instanceof Pp.PpCmdBox) {
        // FIXME: use blockType
        // FIXME: boxes used to have a list, but now glues have lists, so not sure this makes sense anymore
        return box(p, htmlPrintPpCmds([p.contents]))
    }
    if (p instanceof Pp.PpCmdPrintBreak) {
        return ' '.repeat(p.nspaces)
    }
    if (p instanceof Pp.PpCmdForceNewline) {
        return 'TODO: PpCmdForceNewline'
    }
    if (p instanceof Pp.PpCmdComment) {
        return 'TODO: PpCmdComment'
    }
    throw MatchFailure('htmlPrintPpCmd', p)
}

export function htmlPrintPpCmds(l : Pp.t[]) : string {
    _(patterns).each(pattern => {
        l = pattern(l)
    })
        return _.reduce(
            l,
            (acc : string, p : Pp.t) => { return acc + htmlPrintPpCmd(p) },
            ''
        )
}

export function htmlPrintPpCmdsDiff(l : Pp.t[], old : Pp.t[]) : string {
    _(patterns).each(pattern => {
        l = pattern(l)
        old = pattern(old)
    })
        if (!ppCmdsSameShape(l, old)) {
            return markDifferent(
                _.reduce(
                    l,
                    (acc : string, p : Pp.t) => {
                        return acc + htmlPrintPpCmd(p)
                    },
                    ''
                )
            )
        }
    const z = _.zip(l, old)
    return _.reduce(
        z,
        (acc : string, [p, oldP] : [Pp.t, Pp.t]) => {
            return acc + htmlPrintPpCmdDiff(p, oldP)
        },
        ''
    )
}

function ppCmdSameShape(p : Pp.t, old : Pp.t) : boolean {
    return (p.constructor === old.constructor)
}

export function ppCmdsSameShape(l : Pp.t[], old : Pp.t[]) : boolean {
    if (l.length === 0 && old.length === 0) { return true }
    if (l.length > 0 && old.length > 0) {
        return (
            ppCmdSameShape(l[0], old[0])
                && ppCmdsSameShape(l.slice(1), old.slice(1))
        )
    }
    return false
}
