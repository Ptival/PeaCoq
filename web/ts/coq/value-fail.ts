export class ValueFail implements IValueFail {
  public stateId: number
  public location: Maybe<ErrorLocation>
  public message: string
  constructor(v) {
    this.stateId = v[0]
    this.location = nothing()
    if (v[1]) {
      const [startPos, stopPos] = v[1]
      this.location = just({ startPos: startPos, stopPos: stopPos })
    }
    this.message = trimSpacesAround(unbsp(v[2]))
  }
}
