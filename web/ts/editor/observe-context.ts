import * as Context from "./context";
import * as Stage from "./stage";
import * as DebugFlags from "../peacoq/debug-flags";
import { emptyContext } from "../peacoq/peacoq";

export function setup(
  doc: ICoqDocument,
  peaCoqGetContextRouteId: number,
  peaCoqGetContext$: Rx.Subject<ISertop.IControl<ISertop.IControlCommand.IStmQuery>>,
  notice$: Rx.Observable<NoticeMessageFeedback>
) {
  /*
  Feedback comes back untagged, so need the zip to keep track of the relationship
  between input PeaCoqGetContext and the output context...
  */
  Rx.Observable.zip(
    peaCoqGetContext$,
    notice$.filter(m => m.routeId === peaCoqGetContextRouteId)
  ).subscribe(([cmd, fbk]) => {
    // console.log(cmd, fbk);
    const stateId = cmd.controlCommand.queryOptions.sid;
    if (stateId === undefined) { debugger; throw cmd; }
    const rawContext = fbk.feedbackContent.message;
    const sentence = doc.getSentenceByStateId(stateId);
    sentence.caseOf<void>({
      nothing: () => { },
      just: sentence => {
        if (!(sentence.stage instanceof Stage.Processed)) { debugger; }
        const stage: IProcessed = <any>sentence.stage;
        if (DebugFlags.rawPeaCoqContext) { console.log(rawContext); }
        if (rawContext.length === 0) {
          stage.setContext(emptyContext);
        } else {
          const context = Context.create(rawContext);
          stage.setContext(context);
        }
      }
    })
  });
}
