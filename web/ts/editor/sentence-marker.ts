export class SentenceMarker implements ISentenceMarker {
  public klass: string
  public markerId: number
  public markerRange: AceAjax.Range

  constructor(
    public document: ICoqDocument,
    public startPosition: AceAjax.Position,
    public stopPosition: AceAjax.Position
  ) {
    this.klass = "toprocess"
    this.markerRange = new AceAjax.Range(startPosition.row, startPosition.column, stopPosition.row, stopPosition.column)
    this.markerId = document.session.addMarker(this.markerRange, this.klass, "text", false)
  }

  public highlight(): void { this.updateWith("highlight") }

  public markBeingProcessed(): void {
    this.klass = "processing"
    this.update()
  }

  public markProcessed(): void {
    this.klass = "processed"
    this.update()
  }

  public remove(): void {
    this.document.session.removeMarker(this.markerId)
  }

  public unhighlight(): void { this.update() }

  private update(): void { this.updateWith(this.klass) }

  private updateWith(klass: string): void {
    this.document.session.removeMarker(this.markerId)
    this.markerId = this.document.session.addMarker(this.markerRange, klass, "text", false)
  }

}
