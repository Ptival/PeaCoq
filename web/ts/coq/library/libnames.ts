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
    dirpath : Names.DirPath.T
    basename : Names.Id.T
}
type QualId = FullPath

export class Qualid { constructor(public qualId : QualId) { } }
export class Ident { constructor(public id : Names.Id.T) { } }

function reprQualid(q : QualId) : [Names.DirPath.T, Names.Id.T] {
    return reprPath(q)
}

function reprPath(p : FullPath) : [Names.DirPath.T, Names.Id.T] {
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

function prQualid(q : QualId) : Pp.T { return prPath(q) }

export function prReference(r : Reference) : Pp.T {
    return peaCoqBox(C_AST.withVal((r : ReferenceR) => {
        if (r instanceof Qualid) { return prQualid(r.qualId) }
        if (r instanceof Ident) { return Names.Id.print(r.id) }
        debugger
        throw r
    })(r))
}
