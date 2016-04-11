export let coqDocument: ICoqDocument;

export let proofTrees: IProofTree[] = [];

export let tabs: ITabs;

export function getAllEditorTabs(): IEditorTab[] {
  return [
    tabs.foreground,
    tabs.background,
    tabs.shelved,
    tabs.givenUp,
    tabs.notices,
    tabs.warnings,
    tabs.errors,
    tabs.infos,
    tabs.debug,
    tabs.failures,
    // tabs.feedback,
    tabs.jobs,
  ]
}

export function setCoqDocument(d: ICoqDocument) {
  coqDocument = d;
}

export function setTabs(t: ITabs) {
  tabs = t;
}
//
// export let input$ = Rx.Observable.interval(1000).publish();
//
// // input$.subscribe(x => console.log("input", x));
//
// export function process(input$: Rx.Observable<number>) {
//   return input$
//     .concatMap(x => Rx.Observable.return(x).delay(1000))
//     .concatMap(x => {
//       return (
//         x % 10 === 5
//         ? Rx.Observable.throw(new Error("bad"))
//         : Rx.Observable.return(x)
//       );
//     });
// }
//
// export let test = process(input$).catch(() => test);
//
// subscribeAndLog(test);
//
// input$.connect();
