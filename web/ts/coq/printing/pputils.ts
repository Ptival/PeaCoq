import * as Pp from '../lib/pp'

export function prLocated<T>(pr : (t : T) => Pp.t, [loc, x] : Located<T>) {
    // TODO : Flags.beautify?
    return pr(x)
}

export function prAST<T>(pr : (v : T) => Pp.t, ast : cAST<T>) : Pp.t {
    return prLocated(pr, [ast.loc, ast.v])
}
