import * as PeaCoq from "../peacoq/peacoq";

export function createGetCompletions(
  doc: ICoqDocument,
  stopAutomationRound$: Rx.Observable<{}>,
  nextSubject: Rx.Subject<{}>
) {

  doc.editor.execCommand("startAutocomplete");

  // There doesn't seem to be a way to attach a post-insertion handler, but
  // we can hack one together!
  doc.editor.completer.keyboardHandler.bindKeys({
    "Return": editor => {
      Rx.Observable.fromEvent<any>(doc.editor.commands as any, "afterExec")
        .filter(e => e.command.name === "insertstring")
        .take(1)
        .subscribe(() => {
          nextSubject.onNext({});
          (doc.editor as any).exec("insertstring", "\n");
        });
      return editor.completer.insertMatch();
    }
  });

  const popup = doc.editor.completer.getPopup();
  // Ace sometimes triggers show and select like crazy, so debounce it a little
  const show$ = Rx.Observable.fromEvent(popup, "show").debounce(0);
  const hide$ = Rx.Observable.fromEvent(popup, "hide");
  const select$ = Rx.Observable.fromEvent(popup, "select").debounce(0);
  // show$.subscribe(() => console.log("show"));
  // select$.subscribe(() => console.log("select"));

  show$
    .concatMap(() => select$.startWith({}).takeUntil(hide$))
    .map(() => {
      const row = popup.getRow();
      const data = popup.getData(row);
      const sentence: ISentence<IStage> = data.sentence;
      const context = sentence.completions[data.meta][data.caption];
      return { context, sentence };
    })
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
    callback: (err: boolean, results: AceAjax.Completion[], keepPopupPosition: boolean) => void
  ): void {

    const sentenceToComplete = _.maxBy(doc.getAllSentences(), s => s.sentenceId);

    if (sentenceToComplete === undefined) { return callback(false, [], true); }

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
      })),
      true
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
