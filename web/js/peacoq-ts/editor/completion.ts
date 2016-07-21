
export function createGetCompletions(
  doc: ICoqDocument,
  stopAutomationRound$
) {
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
      }))
    );

    sentenceToComplete.completionAdded$
      .takeUntil(stopAutomationRound$)
      .subscribe(({}) => {
        if (editor.completer && editor.completer.popup) {
          const row = editor.completer.popup.getRow();
          editor.execCommand("startAutocomplete");
          editor.completer.popup.setRow(row);
        }
      })

  }
}
