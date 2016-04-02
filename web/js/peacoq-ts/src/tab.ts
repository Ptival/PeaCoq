export let pretty: Tab;

export class Tab {
  caption: string;
  div: JQuery;
  id: string;
  onClickHandlers: Function[];
  onResizeHandlers: Function[];
  panel: string;
  tab: W2UI.W2Tabs;

  constructor(id: string, caption: string, layout: string, panel: string) {
    this.caption = caption;
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
    this.tab.set(this.id, {
      caption: bold ? "<b>" + this.caption + "</b>" : this.caption
    });
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

}
