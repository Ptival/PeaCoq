export function cata<I, O>(f : (v : I) => O, a : O, m : Maybe<I>) : O {
    return m.caseOf({
        nothing : () => a,
        just : v => f(v),
    })
}
