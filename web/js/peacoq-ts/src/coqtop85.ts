import * as CoqDocument from "./coq85";
import EditorTab from "./editor-tab";
import * as FeedbackContent from "./feedback-content";
import PeaCoqGoal from "./goal";
import { coqDocument, pretty, foreground, background, shelved, givenUp, notices, warnings, errors, infos, feedback, failures, debug } from "./setup";

/*
  This queue guarantees that requests are pushed one after the other,
  and that failure of a request cascades and cancels the following ones.
*/
class RequestQueue {
  queue: Promise<any>;
  constructor() {
    this.queue = Promise.resolve();
  }
  push(f: () => Promise<any>): Promise<any> {
    let self = this;
    let res = this.queue.then(function() { return f(); });
    this.queue = res.catch(function() { self.queue = Promise.resolve(); });
    return res;
  }
}

let requests = new RequestQueue();

function unbsp(s: string): string {
  return s.replace(/ /g, ' ');
}

function trimSpacesAround(s: string): string {
  return s.replace(/^\s+|\s+$/g, '');
}

// TODO: This should be made robust to multiple calls (sequencing should be
// enforced)

export type AddReturn = {
  stateId: number;
  eitherNullStateId: number;
  output: string;
}
type AddHandler = (s: string, r: AddReturn) => void;
let peaCoqAddHandlers: AddHandler[] = [];

// function peaCoqAddPrime(s: string): Promise<any> {
//   console.log("Add'", s);
//   let res =
//     coqtop("add'", s)
//       .then(
//       (r) => {
//         r = {
//           "stateId": r[0],
//           "eitherNullStateId": r[1][0],
//           "output": r[1][1],
//         };
//         _(peaCoqAddHandlers).each((h) => { h(s, r); });
//         return r;
//         //console.log("[@" + stateId + "] Added", eitherNullStateId, output);
//       })
//     ;
//   return res;
// }

type EditAtHandler = (sid: number) => void;
let peaCoqEditAtHandlers: EditAtHandler[] = [];

// function peaCoqEditAt(sid: number): Promise<Object> {
//   console.log("EditAt", sid);
//   return coqtop("editat", sid)
//     .then((o) => {
//       _(peaCoqEditAtHandlers).each((h) => { h(sid); });
//       return o;
//     })
//   ;
// }

export type PeaCoqHyp = {
  name: string;
  maybeTerm: Maybe<ConstrExpr>;
  type: ConstrExpr;
};

export type PeaCoqContext = PeaCoqGoal[];

type GetContextHandler = (r: PeaCoqContext) => void;

let peaCoqGetContextHandlers: GetContextHandler[] = [];

// function peaCoqGetContext(): Promise<PeaCoqContext> {
//   return (
//     peaCoqQueryPrime("PeaCoqGetContext.")
//       .then(
//       (c) => {
//         // TODO: don't use eval
//         let rawContext = eval(c);
//         let context = _(rawContext).map((x) => {
//           return new PeaCoqGoal(x.hyps, x.concl);
//         }).value();
//         _(peaCoqGetContextHandlers).each((h) => { h(context); });
//         return context;
//       })
//       .catch(
//       (vf: ValueFail) => {
//         if (vf instanceof ValueFail) {
//           // most likely we are not in proof mode
//           return [];
//         }
//         // otherwise, could be an exception from eval()
//         throw vf;
//       }
//       )
//   );
// }

class Goal {
  goalId: number;
  goalHyp: string[];
  goalCcl: string;

  constructor(g: [string, string[], string]) {
    this.goalId = + g[0];
    this.goalHyp = _(g[1]).map(unbsp).value();
    this.goalCcl = unbsp(g[2]);
  }

  toString(): string {
    let res = "";//"Goal " + this.goalId + "\n\n";
    _(this.goalHyp).each(function(h) {
      res += h + "\n";
    });
    _(_.range(80)).each(function() { res += '-'; });
    res += "\n" + this.goalCcl;
    return res;
  }

}

type GoalBeforeAfter = {
  before: Goal[];
  after: Goal[];
};

export class Goals {
  fgGoals: Goal[];
  bgGoals: GoalBeforeAfter[];
  shelvedGoals: Goal[];
  givenUpGoals: Goal[];

  constructor(maybeGoals) {
    if (!maybeGoals) {
      this.fgGoals = [];
      this.bgGoals = [];
      this.shelvedGoals = [];
      this.givenUpGoals = [];
    } else {
      this.fgGoals = _(maybeGoals[0]).map(function(g) {
        return new Goal(g);
      }).value();
      this.bgGoals = _(maybeGoals[1]).map(function(ba) {
        return {
          "before": _(ba[0]).map(function(b) { return new Goal(b); }).value(),
          "after": _(ba[1]).map(function(b) { return new Goal(b); }).value(),
        };
      }).value();
      this.shelvedGoals = _(maybeGoals[2]).map(function(g) {
        return new Goal(g);
      }).value();
      this.givenUpGoals = _(maybeGoals[3]).map(function(g) {
        return new Goal(g);
      }).value();
    }
  }

}

type GoalHandler = (g: Goals) => void;
let peaCoqGoalHandlers: GoalHandler[] = [];

// function peaCoqGoal(): Promise<Goals> {
//   console.log("Goal");
//   return (
//     coqtop("goal", [])
//       .then(
//       (maybeGoals) => {
//         //console.log("maybeGoals", maybeGoals);
//         let goals = new Goals(maybeGoals);
//         _(peaCoqGoalHandlers).each((h) => { h(goals); })
//         // weird, maybeGoals is an array of length 4 with 3 empty
//         console.log("Goal", goals);
//         return goals;
//       })
//       .catch(
//       (vf: ValueFail) => {
//         return [];
//       }
//       )
//   );
// }

// function peaCoqInit() {
//     console.log("Init");
//     coqtop("init", null, function(sid) {
//         //console.log("Initialized, current state Id: ", sid);
//     });
// }

// function peaCoqQueryPrime(s: string): Promise<string> {
//   console.log("Query'", s);
//   return coqtop("query'", s);
// }

// function peaCoqPrintAST(sid: number): Promise<CoqXMLTree> {
//   console.log("PrintAST", sid);
//   return coqtop("printast", sid).then(function(r) {
//     let tree = new CoqXMLTree(r);
//     console.log("PrintAST\n", r.toString());
//     return tree;
//   });
// }

export class Status {
  statusPath: string[];
  statusProofName: string;
  statusAllProofs: string;
  statusProofNum: number;
  constructor(status) {
    this.statusPath = status[0];
    this.statusProofName = status[1];
    this.statusAllProofs = status[2];
    this.statusProofNum = status[3];
  }
}

type StatusHandler = (s: Status) => void;
let peaCoqStatusHandlers: StatusHandler[] = [];

// function peaCoqStatus(b: boolean): Promise<Status> {
//   console.log("Status");
//   return (
//     coqtop("status", b)
//       .then(
//       (s) => {
//         let status = new Status(s);
//         console.log("Status: ", status);
//         _(peaCoqStatusHandlers).each((h) => { h(status); })
//         return status;
//       })
//   );
// }

export class ValueFail {
  stateId: number;
  location: string;
  message: string;
  constructor(v) {
    this.stateId = v[0];
    this.location = v[1];
    this.message = trimSpacesAround(unbsp(v[2]));
  }
}

function mkMessageLevel(m): MessageLevel {
  switch (m.tag) {
    case "Debug":
      return new Debug(m.contents);
    case "Error":
      return new MyError();
    case "Info":
      return new Info();
    case "Notice":
      return new Notice();
    case "Warning":
      return new Warning();
    default:
      throw ("Unknown message level: " + m.tag);
  };
}

abstract class MessageLevel {
  abstract getAssociatedTab(): EditorTab;
  abstract toString(): string;
}

class Debug extends MessageLevel {
  debug: string;
  constructor(s) {
    super();
    this.debug = s;
  }
  getAssociatedTab() { return debug; }
  toString() {return "Debug(" + this.debug + ")"; }
}

class MyError extends MessageLevel {
  constructor() { super(); }
  getAssociatedTab() { return errors; }
  toString() { return "Error"; }
}

class Info extends MessageLevel {
  constructor() { super(); }
  getAssociatedTab() { return infos; }
  toString() { return "Info"; }
}

class Notice extends MessageLevel {
  constructor() { super(); }
  getAssociatedTab() { return notices; }
  toString() { return "Notice"; }
}

export class Warning extends MessageLevel {
  constructor() { super(); }
  getAssociatedTab() { return warnings; }
  toString() { return "Warning"; }
}

export class Message {
  level: MessageLevel;
  content: string;
  constructor(m) {
    this.level = mkMessageLevel(m[0]);
    this.content = unbsp(m[1]);
  }
  display() {
    let tab = this.level.getAssociatedTab();
    tab.setValue(this.content, false);
  }
  toString() {
    return (
      "[" + this.level.toString() + "]\n" + this.content
    );
  }
}

export class Feedback {
  // TODO: give this a less lame type
  editOrState: string;
  editOrStateId: number;
  feedbackContent: FeedbackContent.FeedbackContent;
  routeId: number;
  constructor(f) {
    switch (f[0].tag) {
      case "State":
        this.editOrState = "state";
        break;
      case "Edit":
        this.editOrState = "edit";
        break;
      default:
        throw "Feedback tag was neither State nor Edit";
    };
    this.editOrStateId = f[0].contents;
    this.feedbackContent = FeedbackContent.create(f[1]);
    this.routeId = f[2];
  }
  toString() {
    return (
      "Feedback(" + this.editOrState + ", " + this.editOrStateId + ", " +
      this.feedbackContent + ", " + this.routeId + ")"
    );
  }
}

class CoqXMLTree {
  rootLabel: LocatedCoqXMLTag;
  subForest: CoqXMLTree[];
  constructor(t) {
    this.rootLabel = new LocatedCoqXMLTag(t[0]);
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

class LocatedCoqXMLTag {
  maybeLocation: any;
  coqXMLTag: CoqXMLTag;
  constructor(t) {
    this.maybeLocation = t[0];
    this.coqXMLTag = mkCoqXMLTag(t[1]);
  }
  toString() {
    return this.coqXMLTag.toString();
  }
}

class CoqXMLTag { }

function mkCoqXMLTag(t): CoqXMLTag {
  let c = t.contents;
  switch (t.tag) {
    case "Apply":
      return new Apply();
    case "Constant":
      return new Constant(c);
    case "Definition":
      return new Definition(c[0], c[1]);
    case "Gallina":
      return new Gallina();
    case "Ltac":
      return new Ltac(c);
    case "Operator":
      return new Operator(c[0], c[1]);
    case "Proof":
      return new Proof();
    case "QED":
      return new QED();
    case "Recurse":
      return new Recurse();
    case "SectionSubsetDescr":
      return new SectionSubsetDescr(c);
    case "Theorem":
      return new Theorem(c[0], c[1]);
    case "Token":
      return new Token(c);
    case "Typed":
      return new Typed();
    default:
      throw ("Unknown CoqXMLTag: " + t.tag);
  };
}

class Apply extends CoqXMLTag {
  toString() { return "Apply"; }
}

class Constant extends CoqXMLTag {
  constant: string;
  constructor(s) {
    super();
    this.constant = s;
  }
  toString() { return "Constant(" + this.constant + ")"; }
}

class Definition extends CoqXMLTag {
  a: string;
  b: string;
  constructor(a, b) {
    super();
    this.a = a;
    this.b = b;
  }
  toString() {
    return "Definition(" + this.a + ", " + this.b + ")";
  }
}

class Gallina extends CoqXMLTag {
  toString = function() { return "Gallina"; }
}

class Ltac extends CoqXMLTag {
  s: string;
  constructor(s) {
    super();
    this.s = s;
  }
  toString() { return "Ltac(" + this.s + ")"; }
}

class Operator extends CoqXMLTag {
  s: string;
  ms: string;
  constructor(s, ms) {
    super();
    this.s = s;
    this.ms = ms;
  }
  toString() { return "Operator(" + this.s + ", " + this.ms + ")"; }
}

class Proof extends CoqXMLTag {
  toString() { return "Proof"; }
}

class QED extends CoqXMLTag {
  toString() { return "QED"; }
}

class Recurse extends CoqXMLTag {
  toString() { return "Recurse"; }
}

class SectionSubsetDescr extends CoqXMLTag {
  s: string;
  constructor(s) {
    super();
    this.s = s;
  }
  toString() { return "SectionSubsetDescr(" + this.s + ")"; }
}

class Theorem extends CoqXMLTag {
  a: string;
  b: string;
  constructor(a, b) {
    super();
    this.a = a;
    this.b = b;
  }
  toString() { return "Theorem(" + this.a + ", " + this.b + ")"; }
}

class Token extends CoqXMLTag {
  s: string;
  constructor(s) {
    super();
    this.s = s;
  }
  toString() { return "Token(" + this.s + ")"; }
}

class Typed extends CoqXMLTag {
  toString() { return "Typed"; }
}
