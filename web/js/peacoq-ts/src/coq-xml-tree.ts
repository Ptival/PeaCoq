import { Located } from "./coq-definitions";
import { CoqXMLTag, mkCoqXMLTag } from "./coq-xml-tag";

export default CoqXMLTree;

export class CoqXMLTree {
  rootLabel: Located<CoqXMLTag>;
  subForest: CoqXMLTree[];
  constructor(t) {
    let [loc, xmltag] = t;
    this.rootLabel = [loc, mkCoqXMLTag(xmltag)];
    this.subForest = _(t[1]).map(function(t) {
      return new CoqXMLTree(t);
    }).value();
  }
  toString(depth: number) {
    let res = "";
    if (typeof depth === "undefined") {
      depth = 0;
    }
    _(_.range(depth)).each(function() {
      res += "  ";
    });
    res += "`- " + this.rootLabel.toString() + "\n";
    _(this.subForest).each(function(t: CoqXMLTree) {
      res += t.toString(depth + 1);
    });
    return res;
  }
}
