/*
The pretty-printed context is exposed objects of the form:
{ constructorName: "Constructor",
  constructorArgs: [a1, ...] }
Where the `a`s may be numerals, strings, arrays or objects
*/

export function walkJSON(input: any): any {
  // console.log(input)
  if (typeof input === "object") {
    if (input.hasOwnProperty("constructorName")) {
      const processedArgs = _(input.constructorArgs).map(walkJSON).value()
      switch (input.constructorName) {
        case "CNotation": {
          const [a, b, c, d, e] = processedArgs
          return new CNotation(a, b, c, d, e)
        }
        case "CPrim": {
          const [a, b] = processedArgs
          return new CPrim(a, b)
        }
        case "CRef": {
          const [a, b] = processedArgs
          return new CRef(a, b)
        }
        case "E": return new E()
        case "Ident": {
          const [a] = processedArgs
          return new Ident(a)
        }
        case "L": return new L()
        case "nothing": return nothing()
        case "Numeral": {
          const [a] = processedArgs
          return new Numeral(a)
        }
        case "PpBrk": {
          const [a, b] = processedArgs
          return new PpBrk(a, b)
        }
        case "PpHoVB": {
          const [a] = processedArgs
          return new PpHoVB(a)
        }
        case "Prec": {
          const [a] = processedArgs
          return new Prec(a)
        }
        case "Qualid": {
          const [a] = processedArgs
          return new Qualid(a)
        }
        case "UnpBox": {
          const [a, b] = processedArgs
          return new UnpBox(a, b)
        }
        case "UnpCut": {
          const [a] = processedArgs
          return new UnpCut(a)
        }
        case "UnpMetaVar": {
          const [a, b] = processedArgs
          return new UnpMetaVar(a, b)
        }
        case "UnpTerminal": {
          const [a] = processedArgs
          return new UnpTerminal(a)
        }
        default:
          const showme = input.constructorName
          const len = input.constructorArgs.length
          debugger
      }
      // return new (eval(input.constructorName))(...processedArgs)
    }
    if (Array.isArray(input)) {
      return _(input).map(walkJSON).value()
    }
    const output: any = {}
    for (const k in input) {
      output[k] = walkJSON(input[k])
    }
    return output
  }
  if (_(["boolean", "number", "string"]).includes(typeof input)) {
    return input
  }
  debugger
  return input
}
