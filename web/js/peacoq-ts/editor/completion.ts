
const names = ["foo", "bar", "baz"];

export function getCompletions(
  editor: AceAjax.Editor,
  session: AceAjax.IEditSession,
  position: AceAjax.Position,
  prefix: string,
  callback: (err: boolean, results: AceAjax.Completion[]) => void
): void {
  callback(
    false,
    names.map(e => ({
      caption: e,
      meta: "static",
      score: 100,
      value: e,
    }))
  );
}
