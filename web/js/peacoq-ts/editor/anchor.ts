
// TODO: one of Anchor and mkAnchor should disappear
class Anchor {
  anchor: AceAjax.Anchor;
  marker: any;
  constructor(
    doc: ICoqDocument,
    row: number,
    column: number,
    klass: string,
    insertRight: boolean
  ) {
    this.anchor = new AceAjax.Anchor(doc.session.getDocument(), row, column);
    if (insertRight) { this.anchor.$insertRight = true; }
    this.marker = {};
    this.marker.update = function(html, markerLayer, session, config) {
      console.log("MARKER UPDATE");
      let screenPos = session.documentToScreenPosition(this.anchor);
      let height = config.lineHeight;
      let width = config.characterWidth;
      let top = markerLayer.$getTop(screenPos.row, config);
      let left = markerLayer.$padding + screenPos.column * width;
      html.push(
        "<div class='", klass, "' style='",
        "height:", height, "px;",
        "top:", top, "px;",
        "left:", left, "px; width:", width, "px'></div>"
      );
    };
    this.marker = doc.session.addDynamicMarker(this.marker, true);
    this.anchor.on("change", function() {
      doc.session._signal("changeFrontMarker");
    });
  }
}
