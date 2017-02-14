// export class SentenceMarker implements ISentenceMarker {
//   private marker: CodeMirror.TextMarker

//   public klass: string
//   public markerRange: IEditorRange

//   constructor(
//     private editor: IEditor,
//     // public document: ICoqDocument,
//     public startPosition: IPosition,
//     public stopPosition: IPosition
//   ) {
//     this.klass = "toprocess"
//     this.markerRange = new EditorRange(startPosition.row, startPosition.col, stopPosition.row, stopPosition.col)
//     this.marker = editor.markText(
//       this.markerRange,
//       this.klass
//     )
//   }

//   public highlight(): void { this.updateWith("highlight") }

//   public markBeingProcessed(): void {
//     this.klass = "processing"
//     this.update()
//   }

//   public markProcessed(): void {
//     this.klass = "processed"
//     this.update()
//   }

//   public remove(): void {
//     this.marker.clear()
//   }

//   public unhighlight(): void { this.update() }

//   private update(): void { this.updateWith(this.klass) }

//   private updateWith(klass: string): void {
//     this.marker.clear()
//     this.marker = this.buffer.addMarker(this.markerRange, klass, "text", false)
//   }

// }
