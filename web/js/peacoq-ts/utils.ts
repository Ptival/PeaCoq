/*
DO NOT TURN THIS FILE INTO A MODULE AS SOME NON-MODULE FILES USE IT!
*/
let tup1: [number, number] = [1, 2, 3];

let tup2: [number, number] = <any>[1, 2, "foo"];
let nbsp = "\u00A0";

function unbsp(s: string): string {
  return s.replace(/ /g, ' ');
}

function trimSpacesAround(s: string): string {
  return s.replace(/^\s+|\s+$/g, '');
}

function replaceNBSPWithSpaces(s: string): string {
  return s.replace(/\u00A0/g, " ");
}

function subscribeAndLog(s: Rx.Observable<any>, info?: string): void {
  s.subscribe(x => { info ? console.log(info, x) : console.log(x); })
}

type Maybe<T> = TsMonad.Maybe<T>;
let nothing = TsMonad.Maybe.nothing;
let just = TsMonad.Maybe.just;

function fromJust<T>(m: Maybe<T>): T {
  return m.caseOf({
    nothing: () => { debugger; return <any>undefined; /* shut up TypeScript! */ },
    just: x => x,
  })
}

function isNothing<T>(m: Maybe<T>): boolean {
  return m.equals(nothing());
}

function isJust<T>(m: Maybe<T>): boolean {
  return m.caseOf({ nothing: () => false, just: x => true });
}

function bindAll<T, U>(l: Maybe<T>[], f: (...args: T[]) => U): Maybe<U> {
  if (l.length === 0) { return just(f()); }
  return l[0].caseOf({
    nothing: () => nothing<U>(),
    just: l0 => {
      return bindAll(l.slice(1), (...args) => f(l0, ...args))
    }
  })
}

function listFromMaybe<T>(m: Maybe<T>): T[] {
  return m.caseOf({ nothing: () => [], just: x => [x] });
}

function assert(condition: boolean, message: string): void {
  if (!condition) {
    alert(`Assertion failed: ${message}`);
    throw message || "Assertion failed";
  }
}

function avg(n1: number, n2: number): number { return (n1 + n2) / 2; }

function parseSVGTransform(a: string): any {
  let b = {};
  let m = a.match(/(\w+\((\-?\d+\.?\d*,? ?)+\))+/g);
  if (m !== null) {
    for (let i in m) {
      let c = m[i].match(/[\w\.\-]+/g);
      if (c !== null) {
        const next = c.shift();
        if (next !== undefined) {
          b[next] = c;
        }
      }
    }
    return b;
  } else {
    debugger;
  }
}

function MatchFailure(fn: string, o: Object) {
  if (!o) { return "undefined discriminee"; }
  return (`Match failed in ${fn}, constructor: ${o.constructor.toString()}`);
}

function MissingOverload(fn: string, o: Object) {
  return (`Missing overload ${fn}, constructor: ${o.constructor.toString()}`);
}

function isUpperCase(character: string): boolean {
  return /^[A-Z]$/.test(character);
}

// specialized version of console.log, because JS is stupid
function outputError(error: any): void {
  console.log(error, error.stack);
}

function mkDot(x: number, y: number): XY { return { "x": x, "y": y }; }

function showDot(d: XY): string { return `${d.x} ${d.y}`; }

/*

  a_____b     c_____d
  |     |     |     |
  h_____g     f_____e

*/
function connectRects(r1: ClientRect, r2: ClientRect, rightsLeft?: number) {
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
    `M${showDot(a)}L${showDot(b)}C${showDot(cp1)},${showDot(cp2)},${showDot(c)}`
    + `L${showDot(d)},${showDot(e)},${showDot(f)}C${showDot(cp3)},${showDot(cp4)}`
    + `,${showDot(g)}L${showDot(h)}Z`
  );
}

function byDiffId(d: Diff): string {
  let res = "{";
  if (d.oldHyp !== null) { res += d.oldHyp.hName; }
  res += "-";
  if (d.newHyp !== null) { res += d.newHyp.hName; }
  return res + "}";
}

function sameNameAs(a: Hypothesis): (b: Hypothesis) => boolean {
  return function(b: Hypothesis) { return a.hName === b.hName; };
}

interface Diff {
  oldHyp: Hypothesis | null;
  newHyp: Hypothesis | null;
  isJump: boolean;
}

function computeDiffList(oldHypsOriginal: Hypothesis[], newHypsOriginal: Hypothesis[]): Diff[] {
  let diffList: Diff[] = [];

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
    // Note: <Hypothesis | undefined> is to allow === under strictNullChecks
    // until TypeScript#843aa6c1effe8365bb461a4a953d55eeb5dfa7cf gets to npm
    let matchesOld = <Hypothesis | undefined>_(newHyps).find(sameNameAs(oldHyp));
    // or the first old has disappeared
    if (matchesOld === undefined) {
      diffList.push({ "oldHyp": oldHyp, "newHyp": null, "isJump": false });
      oldHyps.shift();
      continue;
    }
    // or the first old has moved, but the first new has appeared
    let matchesNew = <Hypothesis | undefined>_(oldHyps).find(sameNameAs(newHyp));
    if (matchesNew === undefined) {
      diffList.push({ "oldHyp": null, "newHyp": newHyp, "isJump": false });
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
    diffList.push({ "oldHyp": oldHyp, "newHyp": null, "isJump": false });
  });

  // now register the remaining appearing
  _(newHyps).each(function(newHyp) {
    diffList.push({ "oldHyp": null, "newHyp": newHyp, "isJump": false });
  });

  return diffList;
}

function repeat(n: number, s: string): string {
  return Array(n + 1).join(s);
}

function prefixes<T>(a: T[]): T[][] {
  return _(a).reduce(
    (acc, elt) =>
      acc.length === 0
        ? [[elt]]
        : [].concat(acc, [[].concat(_(acc).last(), elt)]),
    []
  );
}
