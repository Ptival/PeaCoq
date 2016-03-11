type Maybe<T> = TsMonad.Maybe<T>;
let nothing = TsMonad.Maybe.nothing;
let just = TsMonad.Maybe.just;

function fromJust<T>(m: Maybe<T>): T {
  return m.caseOf<T>({
    nothing: () => undefined,
    just: (x) => x,
  })
}

function isNothing<T>(m: Maybe<T>): boolean {
  return m.equals(nothing());
}

function isJust<T>(m: Maybe<T>): boolean {
  return m.caseOf({ nothing: () => false, just: (x) => true });
}

function bindAll<T, U>(l: Maybe<T>[], f: (...args: T[]) => U): Maybe<U> {
  if (l.length === 0) { return just(f()); }
  return l[0].caseOf({
    nothing: () => nothing<U>(),
    just: (l0) => {
      return bindAll(l.slice(1), (...args) => f(l0, ...args))
    }
  })
}

function assert(condition: boolean, message: string): void {
  if (!condition) {
    alert("Assertion failed: " + message);
    throw message || "Assertion failed";
  }
}

function avg(n1, n2) { return (n1 + n2) / 2; }

function parseSVGTransform(a: string): any {
  let b = {};
  let m = a.match(/(\w+\((\-?\d+\.?\d*,? ?)+\))+/g);
  for (let i in m) {
    let c = m[i].match(/[\w\.\-]+/g);
    b[c.shift()] = c;
  }
  return b;
}

function MatchFailure(fn: string, o: Object) {
  if (!o) { return "undefined discriminee"; }
  return ("Match failed in " + fn + ", constructor: " + o.constructor.toString());
}

function MissingOverload(fn: string, o: Object) {
  return ("Missing overload " + fn + ", constructor: " + o.constructor.toString());
}

function isUpperCase(character) {
  return /^[A-Z]$/.test(character);
}

// specialized version of console.log, because JS is stupid
function outputError(error: any): void {
  console.log(error, error.stack);
}

function mkDot(x, y) { return { "x": x, "y": y }; }

function showDot(d) { return d.x + " " + d.y; }

/*

  a_____b     c_____d
  |     |     |     |
  h_____g     f_____e

*/
function connectRects(r1, r2, rightsLeft) {
  //console.log("rect1", r1, "rect2", r2);
  if (rightsLeft === undefined) { rightsLeft = r2.left; }
  let a = mkDot(r1.left, r1.top);
  let b = mkDot(r1.right, r1.top);
  let c = mkDot(rightsLeft, r2.top);
  let d = mkDot(r2.right, r2.top);
  let e = mkDot(r2.right, r2.bottom);
  let f = mkDot(rightsLeft, r2.bottom);
  let g = mkDot(r1.right, r1.bottom);
  let h = mkDot(r1.left, r1.bottom);

  let cp1 = mkDot(avg(b.x, c.x), b.y);
  let cp2 = mkDot(avg(f.x, g.x), c.y);
  let cp3 = mkDot(avg(f.x, g.x), f.y);
  let cp4 = mkDot(avg(f.x, g.x), g.y);

  //console.log("M", a, b, c, d, e, f, g, h);

  return (
    "M" + showDot(a)
    + "L" + showDot(b)
    + "C" + showDot(cp1) + "," + showDot(cp2) + "," + showDot(c)
    + "L" + showDot(d) + "," + showDot(e) + "," + showDot(f)
    + "C" + showDot(cp3) + "," + showDot(cp4) + "," + showDot(g)
    + "L" + showDot(h)
    + "Z"
  );
}

function byDiffId(d) {
  let res = "{";
  if (d.oldHyp !== undefined) { res += d.oldHyp.hName; }
  res += "-";
  if (d.newHyp !== undefined) { res += d.newHyp.hName; }
  return res + "}";
}

function sameNameAs(a) {
  return function(b) { return a.hName === b.hName; };
}

function computeDiffList(oldHypsOriginal, newHypsOriginal) {
  let diffList = [];

  // slice() creates a shallow copy, since we will mutate this
  let oldHyps = oldHypsOriginal.slice();
  let newHyps = newHypsOriginal.slice();

  while (oldHyps.length > 0 && newHyps.length > 0) {
    let oldHyp = oldHyps[0];
    let newHyp = newHyps[0];
    // either the first two match
    if (oldHyp.hName === newHyp.hName) {
      diffList.push({ "oldHyp": oldHyp, "newHyp": newHyp, "isJump": false });
      oldHyps.shift();
      newHyps.shift();
      continue;
    }
    let matchesOld = _(newHyps).find(sameNameAs(oldHyp));
    // or the first old has disappeared
    if (matchesOld === undefined) {
      diffList.push({ "oldHyp": oldHyp, "newHyp": undefined, "isJump": false });
      oldHyps.shift();
      continue;
    }
    // or the first old has moved, but the first new has appeared
    let matchesNew = _(oldHyps).find(sameNameAs(newHyp));
    if (matchesNew === undefined) {
      diffList.push({ "oldHyp": undefined, "newHyp": newHyp, "isJump": false });
      newHyps.shift();
      continue;
    }
    // otherwise, register matchesOld as a "jump"
    diffList.push({ "oldHyp": oldHyp, "newHyp": matchesOld, "isJump": true });
    oldHyps.shift();
    _(newHyps).remove(sameNameAs(matchesOld));
  }

  // now register the remaining disappearing
  _(oldHyps).each(function(oldHyp) {
    diffList.push({ "oldHyp": oldHyp, "newHyp": undefined, "isJump": false });
  });

  // now register the remaining appearing
  _(newHyps).each(function(newHyp) {
    diffList.push({ "oldHyp": undefined, "newHyp": newHyp, "isJump": false });
  });

  return diffList;
}

/*
  creates an empty rectangle in the same column as [node], at vertical position
  [currentY]
*/
function emptyRect(node: ProofTreeNode, currentY: number): Rectangle {
  let delta = 1; // how big to make the empty rectangle
  return $.extend(
    {
      "left": node.cX,
      "right": node.cX + node.getWidth(),
      "width": node.getWidth()
    },
    {
      "top": currentY - delta,
      "bottom": currentY + delta,
      "height": 2 * delta,
    }
  );
}

function emptyRect0(node: ProofTreeNode, currentY: number): Rectangle {
  let delta = 1; // how big to make the empty rectangle
  return $.extend(
    {
      "left": node.getOriginalScaledX(),
      "right": node.getOriginalScaledY() + node.getWidth(),
      "width": node.getWidth()
    },
    {
      "top": currentY - delta,
      "bottom": currentY + delta,
      "height": 2 * delta,
    }
  );
}

function repeat(n: number, s: string): string {
  return Array(n + 1).join(s);
}

let diffColor = (function() {
  let colors = [
    "#ffbb78",
    "#f7b6d2",
    "#dbdb8d",
    "#6b6ecf",
    "#8ca252",
    "#b5cf6b",
    "#cedb9c",
    "#bd9e39",
    "#d6616b",
    "#ce6dbd",
    "#de9ed6",
  ];
  let scale = d3.scale.ordinal().range(colors);
  return function(n) {
    return scale(n);
  };
})();
