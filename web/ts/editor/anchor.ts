// export class Anchor {
//   public anchor: AceAjax.Anchor
//   public marker: any
//   constructor(
//     doc: ICoqDocument,
//     row: number,
//     column: number,
//     klass: string,
//     insertRight: boolean
//   ) {
//     this.anchor = new AceAjax.Anchor(doc.session.getDocument(), row, column)
//     if (insertRight) { this.anchor.$insertRight = true }
//     this.marker = doc.session.addDynamicMarker(
//       {
//         update: (html: string[], markerLayer: any, session: AceAjax.IEditSession, config: any) => {
//           const { row, column } = this.anchor.getPosition() // they might have been updated since creation time?
//           const screenPos = session.documentToScreenPosition(row, column)
//           const height = config.lineHeight
//           const width = config.characterWidth
//           const top = markerLayer.$getTop(screenPos.row, config)
//           const left = markerLayer.$padding + screenPos.column * width
//           html.push(
//             "<div class='", klass, "' style='",
//             "height:", height, "px",
//             "top:", top, "px",
//             "left:", left, "px width:", width, "px'></div>"
//           )
//         }
//       },
//       true
//     )
//     this.anchor.on("change", () => doc.session._signal("changeFrontMarker"))
//   }
// }
