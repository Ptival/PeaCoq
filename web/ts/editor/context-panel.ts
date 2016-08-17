import { EditorTab } from "./editor-tab";
import { Tab } from "./tab";
import * as VisualizationInteractions from "../visualization-interactions";

export class ContextPanel implements IContextPanel {
  private pretty: ITab;
  private foreground: IEditorTab;
  private background: IEditorTab;
  private shelved: IEditorTab;
  private givenUp: IEditorTab;

  constructor(
    private document: ICoqDocument,
    containerName: string
  ) {
    this.pretty = new Tab("pretty", "Pretty", containerName, "main");
    this.pretty.div.css("padding-left", "4px");
    this.foreground = new EditorTab("foreground", "Foreground", containerName, "main");
    this.background = new EditorTab("background", "Background", containerName, "main");
    this.shelved = new EditorTab("shelved", "Shelved", containerName, "main");
    this.givenUp = new EditorTab("givenup", "Given up", containerName, "main");
  }

  clear(): void {
    this.pretty.div.html("");
    _(this.getAllEditorTabs()).each(t => {
      t.setCaptionSuffix("");
      t.setValue("", false)
    });
  }

  display(c: PeaCoqContext): void {
    this.pretty.div.html("");
    _(c.fgGoals).take(1).each(g => {
      this.pretty.div.append(g.ppgoal.getHTML());
    });
    this.pretty.click();
    // TODO: this should not be done this way!
    VisualizationInteractions.setup();
    // TODO: if performance becomes an issue, do this more lazily?
    this.foreground.setValue(
      _(c.fgGoals).map(g => g.goal.toString()).value().join("\n\n\n"), false
    );
    this.foreground.setCaptionSuffix("(" + c.fgGoals.length + ")");
    const bgGoals = _(c.bgGoals).map((ba) => [].concat(ba.before, ba.after)).flatten().value();
    this.background.setValue(
      _(c.bgGoals).map(ba =>
        _(ba.before).map(g => g.goal.toString()).value().join("\n\n\n")
        +
        _(ba.after).map(g => g.goal.toString()).value().join("\n\n\n")
      ).value().join("\n\n\n"), false
    );
    const nbBgGoals = countBackgroundGoals(c);
    this.background.setCaptionSuffix("(" + nbBgGoals + ")");
    this.shelved.setValue(
      _(c.shelvedGoals).map(g => g.goal.toString()).value().join("\n\n\n"), false
    );
    this.shelved.setCaptionSuffix("(" + c.shelvedGoals.length + ")");
    this.givenUp.setValue(
      _(c.givenUpGoals).map(g => g.goal.toString()).value().join("\n\n\n"), false
    );
    this.givenUp.setCaptionSuffix("(" + c.givenUpGoals.length + ")");
  }

  getAllEditorTabs(): IEditorTab[] {
    return [
      this.foreground,
      this.background,
      this.shelved,
      this.givenUp,
    ];
  }

  onFontSizeChanged(size: number): void {
    _(this.getAllEditorTabs()).each(e => {
      e.setFontSize(size);
    });
  }

  onResize(): void {
    _(this.getAllEditorTabs()).each(e => e.resize());
  }

  setTheme(theme: string): void {
    _(this.getAllEditorTabs()).each(et => { et.setTheme(theme); });
  }

}

function countBackgroundGoals<T>(goals: IGoals<T>): number {
  return _.reduce(
    goals.bgGoals,
    (acc, elt) => acc + elt.before.length + elt.after.length,
    0
  );
}
