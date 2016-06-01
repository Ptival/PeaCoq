import * as MessageLevel from "../coq/message-level";

const maxMessagesOnScreen = 2;

export class CoqtopPanel {
  constructor(
    private container: JQuery,
    private error$: Rx.Observable<IValueFail>,
    private message$: Rx.Observable<IMessage>
  ) {
    error$.subscribe(e => this.addAlert(e.message, "danger"));
    message$.groupBy(m => m.level.constructor).subscribe(
      group => group.subscribe(m => this.addAlert(m.content, classify(m.level)))
    );
  }

  addAlert(message, klass) {
    this.container.prepend(makeAlert(message, klass));
    this.container.children().slice(maxMessagesOnScreen).remove();
  }
}

function makeAlert(message, klass) {
  return $("<div>")
    .text(message)
    .addClass(`alert alert-${klass}`)
    .css("font-family", "monospace")
    .css("margin-bottom", "2px")
    .css("white-space", "pre");
}

function classify(level: IMessageLevel) {
  switch (level.constructor) {
    case MessageLevel.Debug: return "default";
    case MessageLevel.Error: return "danger";
    case MessageLevel.Info: return "info";
    case MessageLevel.Notice: return "success";
    case MessageLevel.Warning: return "warning";
  }
}
