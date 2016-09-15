
export function boolToSexp(b: boolean): string {
  return b ? "True" : "False"
}

export function optionalToSexp<T>(name: string, option: T | undefined, printer?: (t: T) => string): string {
  return option === undefined ? "" : `(${name} ${printer ? printer(option) : option})`
}
