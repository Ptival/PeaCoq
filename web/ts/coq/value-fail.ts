export class ValueFail implements IValueFail {
  public stateId: number
  public location: Maybe<ErrorLocation>
  public message: string
  constructor(v: [number, [number, number] | undefined, string]) {
    this.stateId = v[0]
    this.location = nothing<ErrorLocation>()
    const loc = v[1]
    if (loc !== undefined) {
      const [startPos, stopPos] = loc
      this.location = just({ startPos: startPos, stopPos: stopPos })
    }
    this.message = trimSpacesAround(unbsp(v[2]))
  }
}
