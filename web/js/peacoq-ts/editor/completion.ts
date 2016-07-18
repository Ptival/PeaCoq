
export function createGetCompletions(doc: ICoqDocument) {
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
    // Memory leak: need a .takeUntil
    .take(1)
    .subscribe(({}) => {
        const row = (editor.completer && editor.completer.popup) ? editor.completer.popup.getRow() : 0;
        editor.execCommand("startAutocomplete");
        editor.completer.popup.setRow(row);
    })

  }
}
