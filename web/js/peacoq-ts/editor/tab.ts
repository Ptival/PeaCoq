export class Tab implements ITab {
  private _captionShouldBeBold: boolean;
  private captionSuffix: string;
  div: JQuery;
  // TODO: use Observables
  onClickHandlers: Function[];
  onResizeHandlers: Function[];
  tab: W2UI.W2Tabs;

  constructor(
    public id: string,
    public caption: string,
    layout: string,
    public panel: string
  ) {
    this.caption = caption;
    this.captionSuffix = "";
    this.id = id;
    this.panel = panel;
    let w2uiId = layout + "_" + panel + "_tabs";
    this.tab = w2ui[w2uiId];

    let self = this;

    this.div = $("<div>", { id: id + "-content", style: "height: 100%", text: "" });
    this.onClickHandlers = [];
    this.onResizeHandlers = [];

    this.onClickHandlers.push(function(layout) {
      layout.owner.html(panel, self.div[0]);
    });

    this.tab.add({
      id: id,
      caption: caption,
      onClick: function() { self.onClick(this); }
    });

    $(window).resize(() => {
      _(self.onResizeHandlers).each((h) => { h(); });
    });
  }

  captionShouldBeBold(bold: boolean): void {
    this._captionShouldBeBold = bold;
    this.refresh();
  }

  click(): void {
    this.tab.click(this.id);
  }

  onClick(layout) {
    this.captionShouldBeBold(false);
    _(this.onClickHandlers).each((h) => { h(layout); });
  }

  onResize() {
    _(this.onResizeHandlers).each((h) => { h(); });
  }

  refresh(): void {
    let captionText = `${this.caption} ${this.captionSuffix}`;
    this.tab.set(this.id, {
      caption: this._captionShouldBeBold ? `<b>${captionText}</b>` : captionText
    });
    this.tab.refresh();
  }

  setCaptionSuffix(s: string): void {
    this.captionSuffix = s;
    this.refresh();
  }

}
