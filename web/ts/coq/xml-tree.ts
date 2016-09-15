// import { CoqXMLTag, mkCoqXMLTag } from "./xml-tag"

class CoqXMLTree {
  public rootLabel: Located<CoqXMLTag>
  public subForest: CoqXMLTree[]
  constructor(t: [CoqLocation, ICoqtopResponse<any>]) {
    let [loc, xmltag] = t
    this.rootLabel = [loc, mkCoqXMLTag(xmltag)]
    this.subForest = _(t[1]).map(function(t: [CoqLocation, ICoqtopResponse<any>]) {
      return new CoqXMLTree(t)
    }).value()
  }
  public toString(depth: number) {
    let res = ""
    if (typeof depth === "undefined") {
      depth = 0
    }
    _(_.range(depth)).each(function() {
      res += "  "
    })
    res += "`- " + this.rootLabel.toString() + "\n"
    _(this.subForest).each(function(t: CoqXMLTree) {
      res += t.toString(depth + 1)
    })
    return res
  }
}
