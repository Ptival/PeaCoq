import * as MessageLevel from "../coq/message-level";

const maxMessagesOnScreen = 10;

export class CoqtopPanel {
  constructor(
    private container: JQuery,
    message$: Rx.Observable<{ message: string; level: PeaCoqMessageLevel }>,
    loadedFile$: Rx.Observable<{}>
  ) {
    message$.subscribe(m => this.addAlert(m.message, peaCoqMessageLevelToString(m.level)));
    loadedFile$.subscribe(() => this.container.empty());
  }

  addAlert(message: string, klass: string) {
    this.container.prepend(makeAlert(message, klass));
    this.container.children().slice(maxMessagesOnScreen).remove();
  }
}

function makeAlert(message: string, klass: string) {
  return $("<div>")
    .text(message)
    .addClass(`alert alert-${klass}`)
    .css("font-family", "monospace")
    .css("margin-bottom", "2px")
    .css("padding", "2px")
    .css("white-space", "pre");
}

function classify(level: IMessageLevel): PeaCoqMessageLevel {
  switch (level.constructor) {
    case MessageLevel.Debug: return PeaCoqMessageLevel.Default;
    case MessageLevel.Error: return PeaCoqMessageLevel.Danger;
    case MessageLevel.Info: return PeaCoqMessageLevel.Info;
    case MessageLevel.Notice: return PeaCoqMessageLevel.Success;
    case MessageLevel.Warning: return PeaCoqMessageLevel.Warning;
  }
  throw "CoqtopPanel.classigy";
}

function peaCoqMessageLevelToString(level: IMessageLevel): string {
  switch (level) {
    case PeaCoqMessageLevel.Default: return "default";
    case PeaCoqMessageLevel.Danger: return "danger";
    case PeaCoqMessageLevel.Info: return "info";
    case PeaCoqMessageLevel.Success: return "success";
    case PeaCoqMessageLevel.Warning: return "warning";
  }
  throw "CoqtopPanel.peaCoqMessageLevelToString";
}
