class Tab {
  caption: string;
  div: JQuery;
  id: string;
  onClickHandlers: Function[];
  onResizeHandlers: Function[];
  panel: string;
  w2uiId: string;

  constructor(id: string, caption: string, layout: string, panel: string) {
    this.caption = caption;
    this.id = id;
    this.panel = panel;
    this.w2uiId = layout + "_" + panel + "_tabs";

    let self = this;

    this.div = $("<div>", { id: id + "-content", style: "height: 100%", text: "" });
    this.onClickHandlers = [];
    this.onResizeHandlers = [];

    this.onClickHandlers.push(function(layout) {
      layout.owner.html(panel, self.div[0]);
    });

    w2ui[this.w2uiId].add({
      id: id,
      caption: caption,
      onClick: function() { self.onClick(this); }
    });

    $(window).resize(() => {
      _(self.onResizeHandlers).each((h) => { h(); });
    });
  }

  captionShouldBeBold(bold: boolean): void {
    w2ui[this.w2uiId].set(this.id, {
      caption: bold ? "<b>" + this.caption + "</b>" : this.caption
    });
  }

  click(): void {
    w2ui[this.w2uiId].click(this.id);
  }

  onClick(layout) {
    this.captionShouldBeBold(false);
    _(this.onClickHandlers).each((h) => { h(layout); });
  }

  onResize() {
    _(this.onResizeHandlers).each((h) => { h(); });
  }

}
