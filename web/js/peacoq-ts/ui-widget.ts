@component("ui-widget")

@style(`
.ui-widget {
  background-color: #EEE;
  border: 1px solid black;
  width: var(--ui-widget-width)px;
  height: var(--ui-widget-height)px;
  float: left;
}
.handle {
  background-color: #333;
  float: left;
  width: 10px;
  height: 10px;
  margin-left: 2px;
  margin-top: 2px;
}
:host ::content .ui-icon {
  background-image: url("");
}
`)

@template(`
<div class="ui-widget draggable">
  <div class="handle"></div>
  <content></content>
</div>
`)

class UIWidget extends polymer.Base {
  @property({ type: Number, value: 100 })
  public height: number;
  @property({ type: Number, value: 100 })
  public width: number;

  constructor() {
    super();
  }

  @listen("click")
  onClick() {
  }

  ready() {
    $(this)
      .find(".draggable")
      .draggable({
        grid: [10, 10],
        handle: ".handle",
      })
      .resizable({
        // animate: true,
        handles: "all",
        minWidth: 100,
        minHeight: 100,
        resize: (event, ui) => {
          const increment = 40;
          ui.size.height = Math.round(ui.size.height / increment) * increment;
          ui.size.width = Math.round(ui.size.width / increment) * increment;
        },
      });
  }
}

UIWidget.register();
