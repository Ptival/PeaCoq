// import { ConstrExpr } from "./coq-constr-expr";
// import { PeaCoqGoal } from "./peacoq-goal";

/*
  This queue guarantees that requests are pushed one after the other,
  and that failure of a request cascades and cancels the following ones.
*/
// class RequestQueue {
//   queue: Promise<any>;
//   constructor() {
//     this.queue = Promise.resolve();
//   }
//   push(f: () => Promise<any>): Promise<any> {
//     let self = this;
//     let res = this.queue.then(function() { return f(); });
//     this.queue = res.catch(function() { self.queue = Promise.resolve(); });
//     return res;
//   }
// }
//
// let requests = new RequestQueue();

// TODO: This should be made robust to multiple calls (sequencing should be
// enforced)


// type AddHandler = (s: string, r: AddReturn) => void;
// let peaCoqAddHandlers: AddHandler[] = [];

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

// type EditAtHandler = (sid: number) => void;
// let peaCoqEditAtHandlers: EditAtHandler[] = [];

// function peaCoqEditAt(sid: number): Promise<Object> {
//   console.log("EditAt", sid);
//   return coqtop("editat", sid)
//     .then((o) => {
//       _(peaCoqEditAtHandlers).each((h) => { h(sid); });
//       return o;
//     })
//   ;
// }

// type GetContextHandler = (r: PeaCoqContext) => void;
// let peaCoqGetContextHandlers: GetContextHandler[] = [];

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

// type GoalHandler = (g: Goals) => void;
// let peaCoqGoalHandlers: GoalHandler[] = [];

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

// type StatusHandler = (s: Status) => void;
// let peaCoqStatusHandlers: StatusHandler[] = [];

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
