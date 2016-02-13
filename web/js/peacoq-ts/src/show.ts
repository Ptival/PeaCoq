
// function showBindersPar(t) {
//   if (_.isEmpty(t)) { return ""; }
//   return " (" + showBinder(t[0]) + ")" + showBindersPar(_(t).rest().value());
// }
//
// function showBinders(t) {
//   if (_.isEmpty(t)) { return ""; }
//   if (t.length === 1) { return ' ' + showBinder(t[0]); }
//   return " (" + showBinder(t[0]) + ")" + showBindersPar(_(t).rest().value());
// }
//
// function showBinder(t) {
//   if (t[1] === null) {
//     return showNames(t[0]);
//   } else {
//     return showNames(t[0]) + syntax(":") + ' ' + showTermAux(t[1], 0, 0, false);
//   }
// }
//
// function showPatternAux(p, withParens) {
//   let c = p.contents;
//   switch (p.tag) {
//     case "Wildcard":
//       return "_";
//
//     case "Pattern":
//       if (c[1].length === 0) { // constructor with no parameters, never parenthesized
//         return c[0];
//       } else { // constructor with parameters, parenthesized if subpattern
//         if (c[0] === "cons" && c[1].length === 2) {
//           return (withParens ? syntax("(") : "")
//             + showPatternAux(c[1][0], true)
//             + ' ' + syntax("::") + ' '
//             + showPattern(c[1][1])
//             + (withParens ? syntax(")") : "")
//             ;
//         } else {
//           return (withParens ? syntax("(") : "")
//             + _(c[1]).reduce(function(acc, elt) {
//               return acc + " " + showPatternAux(elt, true);
//             }, c[0])
//             + (withParens ? syntax(")") : "")
//             ;
//         }
//       }
//
//     case "OrPatterns":
//       let patterns = c[0];
//       return (
//         syntax("(")
//         + _(patterns).reduce(function(acc, orpattern, ndx) {
//           return (
//             (ndx > 0 ? syntax(",") : "")
//             + _(orpattern).reduce(function(acc, pattern, ndx) {
//               return (
//                 (ndx > 0 ? "|" : "")
//                 + showPatternAux(pattern, false)
//               );
//             })
//           );
//         })
//         + syntax(")")
//       );
//
//     default:
//       alert("Unknown pattern: " + p.tag);
//
//   };
// }
//
// function showPattern(p) { return showPatternAux(p, false); }
//
// function showPatterns(ps) {
//   if (ps.length === 1) {
//     let patterns = ps[0];
//     return _(patterns).rest().reduce(function(acc, pattern) {
//       return acc + syntax(", ") + showPattern(pattern);
//     }, showPattern(patterns[0]));
//   } else {
//     alert("TODO");
//   }
// }
//
// function showName(t) {
//   if (t === null) { // underscore
//     return ident('_');
//   } else {
//     return ident(t);
//   }
// }
//
// function showNames(t) {
//   if (_.isEmpty(t)) { return ""; }
//
//   return showName(t[0]) + " " + showNames(_(t).rest().value());
// }
//
// function showTerm(t) {
//   let term = mkTerm(t);
//   console.log(term, term.toString());
//   return showTermAux(t, 0, 0, true);
// }
//
// function showTermIndent(t, indent) {
//   return showTermAux(t, indent, 0, true);
// }
//
// function getIndent(depth) {
//   return repeat(2 * depth, " ");
// }
//
// function extractGoal(gGoal) {
//
//   if (gGoal.hasOwnProperty("Left")) {
//     gGoal = {
//       "contents": gGoal.Left,
//       "tag": "Raw",
//     };
//   } else {
//     gGoal = gGoal.Right;
//   }
//
//   return gGoal;
//
// }
//
// function extractHypothesis(gHyp) {
//
//   if (gHyp.hasOwnProperty("Left")) {
//     // this tries to approximate parsing...
//     let matches = gHyp.Left.match(/^([\s\S]*) := ([\s\S]*) : ([\s\S]*)$/);
//     if (matches !== null) {
//       gHyp = {
//         "hName": matches[1],
//         "hValue": { "contents": matches[2], "tag": "Raw" },
//         "hType": { "contents": matches[3], "tag": "Raw" },
//       };
//     } else {
//       matches = gHyp.Left.match(/^([\s\S]*) : ([\s\S]*)$/);
//       gHyp = {
//         "hName": matches[1],
//         "hValue": null,
//         "hType": { "contents": matches[2], "tag": "Raw" },
//       };
//     }
//     if (matches == null) {
//       console.log("could not extract hypothesis", gHyp);
//     }
//
//   } else {
//     gHyp = gHyp.Right;
//   }
//
//   return gHyp;
//
// }
//
// function vernac(s) { return '<span class="vernac">' + s + '</span>'; }
function syntax(s) { return '<span class="syntax">' + s + '</span>'; }
// function ident(s) { return '<span class="identifier">' + s + '</span>'; }
// function term(s) { return '<span class="term">' + s + '</span>'; }
//
// function showConstructor(t) {
//   let name = t[0];
//   if (t[1] === null) {
//     return syntax("|")
//       + ' '
//       + ident(name)
//       ;
//   } else {
//     let type = showTermInline(t[1]);
//     return syntax("|")
//       + ' '
//       + ident(name)
//       + ' '
//       + syntax(":")
//       + ' '
//       + type
//       ;
//   }
// }
//
// function showVernac(t) {
//   let c = t.contents;
//   let args, name, term, type;
//
//   switch (t.tag) {
//
//     case "Inductive":
//       name = c[0];
//       type = showTermInline(c[1]);
//       let constructors = _(c[2]).map(showConstructor);
//       return vernac("Inductive")
//         + ' '
//         + ident(name)
//         + ' '
//         + syntax(":")
//         + ' '
//         + type
//         + ' '
//         + syntax(":=")
//         + "<br>"
//         + _(constructors).reduce(function(acc, elt) { return acc + elt + "<br>"; }, "")
//         + syntax(".")
//         ;
//
//     case "Theorem":
//       name = c[0];
//       type = showTermInline(c[1]);
//       return vernac("Theorem")
//         + ' '
//         + ident(name)
//         + ' '
//         + syntax(":")
//         + ' '
//         + type
//         + syntax(".")
//         ;
//
//     case "Definition":
//       name = c[0];
//       args = _(c[1]).map(showBinder);
//       type = (c[2] !== null)
//         ? syntax(":") + ' ' + showTermInline(c[2]) + ' '
//         : "";
//       term = showTermIndent(c[3], 1);
//       return vernac("Definition")
//         + ' '
//         + ident(name)
//         + ' '
//         + _(args).reduce(function(acc, elt) {
//           return acc + syntax("(") + elt + syntax(")") + ' ';
//         }, "")
//         + type
//         + syntax(":=")
//         + "<br>" + getIndent(1)
//         + term
//         + syntax(".")
//         ;
//
//     case "Fixpoint":
//       name = c[0];
//       args = _(c[1]).map(showBinder);
//       let decreasing = c[2];
//       type = (c[3] !== null)
//         ? syntax(":") + ' ' + showTermInline(c[3]) + ' '
//         : "";
//       term = showTermIndent(c[4], 1);
//       return vernac("Fixpoint")
//         + ' '
//         + ident(name)
//         + ' '
//         + _(args).reduce(function(acc, elt) {
//           return acc + syntax("(") + elt + syntax(")") + ' ';
//         }, "")
//         + (
//           (decreasing !== null)
//             ? syntax("{") + ' ' + syntax("struct")
//             + ' ' + decreasing + ' ' + syntax("}") + ' '
//             : ""
//         )
//         + type
//         + syntax(":=")
//         + "<br>" + getIndent(1)
//         + term
//         + syntax(".")
//         ;
//
//     default:
//       return "Unknown Vernacular tag: " + t.tag;
//
//   };
// }
//
// function showTermText(t) {
//   return $(showTermInline(t)).text();
// }
//
// function showMatchItems(items) {
//   return _(items).reduce(function(acc, item, ndx) {
//     let term = item[0];
//     let matchAs = item[1];
//     let matchIn = item[2];
//     return (
//       acc
//       + (ndx > 0 ? syntax(",") + ' ' : "")
//       + showTermInline(term)
//       + (matchAs ? ' ' + syntax("as") + ' ' + matchAs : "")
//       + (matchIn ? ' ' + syntax("in") + ' ' + showTermInline(matchIn) : "")
//     );
//   }, "");
// }
//
// /*
//   [t]           the term to show
//   [indentation] the indentation to use if you make a newline
//   [precParent]  the precedence of the parent operator (for parenthesizing)
//   [newline]     true if the term should feel free to use multiple lines
// */
// function showTermAux(t, indentation, precParent, newline) {
//   let c = t.contents;
//
//   let indent = getIndent(indentation);
//
//   let par = function(precOp, text) {
//     if (precOp <= precParent) {
//       return term(syntax("(") + text + syntax(")"));
//     } else {
//       return term(text);
//     }
//   };
//
//   let showOp = function(c, op, precOp) {
//     return par(
//       precOp,
//       showTermAux(c[0].contents[1], 0, precOp, false)
//       + " " + syntax(op) + " "
//       + showTermAux(c[1], 0, precOp, false)
//     );
//   };
//
//   switch (t.tag) {
//
//     case "Raw":
//       return '<span>' + c + '</span>';
//
//     case "Var":
//       if (t.type !== undefined) {
//         return '<span style="font-weight: bold;"'
//           + ' title="' + t.type + '">'
//           + c + '</span>'
//           ;
//       } else {
//         return term(c);
//       }
//
//     case "Forall":
//       return par(
//         precForall,
//         syntax("forall") + showBinders(c[0]) + syntax(",")
//         + (newline ? "<br/>" + getIndent(indentation + 1) : " ")
//         + showTermAux(c[1], indentation + 1, precParent, newline)
//       );
//
//     case "Lambda":
//       return par(
//         precMin,
//         syntax("fun") + showBinders(c[0]) + ' ' + syntax("=>")
//         + (newline ? "<br/>" + getIndent(indentation + 1) : " ")
//         + showTermAux(c[1], indentation + 1, precMin, newline)
//       );
//
//     case "Exists":
//       return par(
//         precForall,
//         syntax("exists") + showBinders(c[0]) + syntax(",")
//         + (newline ? "<br/>" + getIndent(indentation + 1) : " ")
//         + showTermAux(c[1], indentation + 1, precParent, newline)
//       );
//
//     case "Arrow":
//       return term(
//         showTermAux(c[0], indentation, precArrow, false)
//         + ' ' + syntax("->")
//         + (newline ? "<br/>" + indent : " ")
//         + showTermAux(c[1], indentation, precParent, newline)
//       );
//
//     case "Match":
//       let matchItems = c[0];
//       let maybeType = c[1];
//       let equations = c[2];
//       return term(
//         syntax("match") + ' '
//         + showMatchItems(matchItems) + ' '
//         + (maybeType
//           ? syntax(":") + ' ' + showTermAux(c[1], 0, precMin, false)
//           : ""
//         )
//         + syntax("with") + "<br>"
//         + _(equations).reduce(function(acc, elt) {
//           let patterns = showPatterns(elt[0]);
//           let body = showTermAux(elt[1], indentation + 1, precParent, newline);
//           return acc
//             + getIndent(indentation) + syntax("|") + ' '
//             + patterns
//             + ' '
//             + syntax("=>")
//             + (
//               (body.indexOf("<br>") === -1)
//                 ? ' ' + body
//                 : "<br>" + getIndent(indentation + 1) + body
//             )
//             + "<br>";
//         }, "")
//         //showTermAux(c[0], indentation, precArrow, false)
//         + getIndent(indentation) + syntax("end")
//       );
//
//     case "App":
//
//       // handling special case of infix operators I want to pretty print
//       if (c[0].contents === "not"
//         && c[1].contents[0].contents[0].contents === "eq"
//       ) {
//         return par(
//           precNotEqual,
//           showTermAux(c[1].contents[0].contents[1], 0, precNotEqual, false)
//           + " ≠ "
//           + showTermAux(c[1].contents[1], 0, precNotEqual, false)
//         )
//       }
//
//       if (c[0].tag === "App") {
//         switch (c[0].contents[0].contents) {
//
//           case "eq":
//             return showOp(c, "=", precEqual);
//
//           case "plus":
//             return showOp(c, "+", precPlus);
//
//           case "minus":
//             return showOp(c, "-", precMinus);
//
//           case "mult":
//             return showOp(c, "*", precMult);
//
//           case "and":
//             return showOp(c, "/\\", precAnd);
//
//           case "or":
//             return showOp(c, "\\/", precOr);
//
//           case "andb":
//             return showOp(c, "&&", precAndB);
//
//           case "orb":
//             return showOp(c, "||", precOrB);
//
//           case "iff":
//             return showOp(c, "<->", precEquiv);
//
//           // case "cons":
//           //     return showOp(c, "::", precCons);
//
//           // case "app":
//           //     return showOp(c, "++", precAppend);
//
//           default:
//           // nothing, fall through
//
//         };
//       }
//
//       return par(
//         precApp,
//         showTermAux(c[0], 0, precApp - 1, false) + " "
//         + showTermAux(c[1], 0, precApp, false)
//       );
//
//     default:
//       return "Unknown tag " + t.tag;
//
//   };
// }
//
// function inlineBlock(contents) {
//   return '<div style="display: inline-block; max-width: 100%; vertical-align: top;">' + contents + '</div>';
// }
//
// function showHypothesis(h) {
//   let res = h.hName;
//   if (h.hValue !== null) {
//     res = res + ' ' + syntax(":=") + ' ' + showTermInline(h.hValue);
//   }
//   res = inlineBlock(res + ' ' + syntax(":") + ' ')
//     + inlineBlock(showTermInline(h.hType));
//   return res;
// }
//
// function showHypothesisText(h) {
//   let res = h.hName;
//   if (h.hValue !== null) {
//     res = res + " := " + showTermText(h.hValue);
//   }
//   res = res + " : " + showTermText(h.hType);
//   return res;
// }
//
// function showTermInline(t) {
//   return showTermAux(t, 0, 0, false);
// }

/*
function getResponseFocused(response) {
  return response.rGoals.focused;
}

function getResponseUnfocused(response) {
  return response.rGoals.unfocused;
}
*/
