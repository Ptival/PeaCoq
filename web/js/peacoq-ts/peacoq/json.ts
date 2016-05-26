/*
The pretty-printed context is exposed objects of the form:
{ constructorName: "Constructor",
  constructorArgs: [a1, ...] }
Where the `a`s may be numerals, strings, arrays or objects
*/

export function walkJSON(input: any): any {
  // console.log(input);
  if (typeof input === "object") {
    if (input.hasOwnProperty("constructorName")) {
      const processedArgs = _(input.constructorArgs).map(walkJSON).value();
      return new (eval(input.constructorName))(...processedArgs);
    }
    if (Array.isArray(input)) {
      return _(input).map(walkJSON).value();
    }
    const output: any = {};
    for (const k in input) {
      output[k] = walkJSON(input[k]);
    }
    return output;
  }
  if (_(["boolean", "number", "string"]).includes(typeof input)) {
    return input;
  }
  debugger;
  return input;
}
