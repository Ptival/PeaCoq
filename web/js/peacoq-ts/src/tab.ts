class Tab {
  div: JQuery;
  onClickHandlers: Function[];
  onResizeHandlers: Function[];

  constructor(id: string, caption: string, layout: string, panel: string) {
    let self = this;
    this.div = $("<div>", { id: id + "-content", style: "height: 100%", text: caption });
    this.onClickHandlers = [];
    this.onResizeHandlers = [];

    this.onClickHandlers.push(function(layout) {
      layout.owner.html(panel, self.div[0]);
    });

    w2ui[layout + "_" + panel + "_tabs"].add({
      id: id,
      caption: caption,
      onClick: function() { self.onClick(this); }
    });

    $(window).resize(() => {
      _(self.onResizeHandlers).each((h) => { h(); });
    });
  }

  onClick(layout) {
    _(this.onClickHandlers).each((h) => { h(layout); });
  }

  onResize() {
    _(this.onResizeHandlers).each((h) => { h(); });
  }

}
