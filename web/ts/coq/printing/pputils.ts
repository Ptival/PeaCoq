import { C_AST } from '../lib/c-ast'
import { Located } from '../lib/loc'
import * as Pp from '../lib/pp'

export function prLocated<T>(pr : (t : T) => Pp.T, [loc, x] : Located<T>) {
    // TODO : Flags.beautify?
    return pr(x)
}

export function prAST<T>(pr : (v : T) => Pp.T, ast : C_AST<T>) : Pp.T {
    return prLocated(pr, [ast.loc, ast.v])
}
