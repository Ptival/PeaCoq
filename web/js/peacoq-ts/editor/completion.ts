import * as PeaCoq from "../peacoq/peacoq";

export function createGetCompletions(
  doc: ICoqDocument,
  stopAutomationRound$
) {

  doc.editor.execCommand("startAutocomplete");

  const popup = doc.editor.completer.getPopup();
  const show$ = Rx.Observable.fromEvent(popup, "show");
  const hide$ = Rx.Observable.fromEvent(popup, "hide");
  const select$ = Rx.Observable.fromEvent(popup, "select");
  // show$.subscribe(() => console.log("show"));
  // select$.subscribe(() => console.log("select"));
  const contextPreview$ = show$
    .concatMap(() => select$.startWith({}).takeUntil(hide$).doOnCompleted(() => console.log("This one is done")))
    .map(() => {
      const row = popup.getRow();
      const data = popup.getData(row);
      const sentence: ISentence<IStage> = data.sentence;
      const context = sentence.completions[data.meta][data.caption];
      return { context, sentence };
    });
  contextPreview$
    .subscribe(({ context, sentence }) => {
      doc.contextPanel.display(context);
      // console.log(data.caption, completion);
    });
  hide$
    .concatMap(() => {
      // when the suggestion panel hides, we should display either:
      // - the sentence at the cursor position if any
      // - the last sentence otherwise
      const sentenceToDisplay =
        doc.getSentenceAtPosition(doc.editor.getCursorPosition())
        .caseOf({
          just: s => s,
          nothing: () => _.maxBy(doc.getAllSentences(), s => s.sentenceId),
        });
      return (
        sentenceToDisplay === undefined
          ? Rx.Observable.just(PeaCoq.emptyContext)
          : sentenceToDisplay.getProcessed$().concatMap(stage => stage.getContext())
      );
    })
    .subscribe(context => doc.contextPanel.display(context));

  return function getCompletions(
    editor: AceAjax.Editor,
    session: AceAjax.IEditSession,
    position: AceAjax.Position,
    prefix: string,
    callback: (err: boolean, results: AceAjax.Completion[]) => void
  ): void {

    const sentenceToComplete = _.maxBy(doc.getAllSentences(), s => s.sentenceId);

    if (sentenceToComplete === undefined) { return callback(false, []); }

    const completions = sentenceToComplete.completions;

    const completionList =
      _.flatMap(
        _.keys(completions),
        group => _.map(
          _.keys(completions[group]),
          tactic => ({
            tactic,
            group,
            context: completions[group][tactic]
          })
        )
      );

    callback(
      false,
      completionList.map(({ tactic, group, context }) => ({
        caption: tactic,
        meta: group,
        score: 100,
        value: tactic,
        sentence: sentenceToComplete,
      }))
    );

    sentenceToComplete.completionAdded$
      .takeUntil(stopAutomationRound$)
      .subscribe(({}) => {
        if (editor.completer && editor.completer.popup) {
          const row = editor.completer.popup.getRow();
          editor.completer.updateCompletions();
          editor.completer.popup.setRow(row);
        }
      })

  }
}
