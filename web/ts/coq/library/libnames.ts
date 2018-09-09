import * as Names from "../kernel/names"
import * as C_AST from "../lib/c-ast"
import { cAST } from "../lib/c-ast"
import * as Pp from "../lib/pp"
import { peaCoqBox } from "../../peacoq/coq-utils"

export type Reference = cAST<ReferenceR>

export type ReferenceR
    = Qualid
    | Ident

type FullPath = {
    dirpath : Names.DirPath.t
    basename : Names.Id.t
}
type QualId = FullPath

export class Qualid { constructor(public qualId : QualId) { } }
export class Ident { constructor(public id : Names.Id.t) { } }

function reprQualid(q : QualId) : [Names.DirPath.t, Names.Id.t] {
    return reprPath(q)
}

function reprPath(p : FullPath) : [Names.DirPath.t, Names.Id.t] {
    return [p.dirpath, p.basename]
}

function stringOfPath(sp : FullPath) {
    const [sl, id] = reprPath(sp)
    if (Names.DirPath.repr(sl).length === 0) {
        return Names.Id.toString(id)
    } else {
        return `${Names.DirPath.toString(sl)}.${Names.Id.toString(id)}`
    }
}

function prPath(sp : FullPath) { return Pp.str(stringOfPath(sp)) }

function prQualid(q : QualId) : Pp.t { return prPath(q) }

export function prReference(r : Reference) : Pp.t {
    return peaCoqBox(C_AST.withVal((r : ReferenceR) => {
        if (r instanceof Qualid) { return prQualid(r.qualId) }
        if (r instanceof Ident) { return Names.Id.print(r.id) }
        throw r
    })(r))
}
