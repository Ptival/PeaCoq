export const rightLayoutName = "right-layout";
export const bottomLayoutName = "bottom-layout";

export function setup(): any {

  $("#interface").w2layout({
    name: "layout",
    panels: [
      { type: "top", size: 34, resizable: false, content: $("<div>", { id: "toolbar" }) },
      { type: "left", size: "50%", overflow: "hidden", resizable: true, content: $("<div>", { id: "editor", style: "height: 100%" }) },
      { type: "main", size: "50%", overflow: "hidden", content: $("<div>", { id: "right" }) },
      { type: "bottom", size: "50%", overflow: "hidden", resizable: false, content: $("<div>", { id: "bottom" }) },
    ]
  });

  $().w2layout({
    name: rightLayoutName,
    panels: [
      { type: "main", size: "50%", resizable: true, tabs: { tabs: [], } },
      { type: "bottom", size: "50%", resizable: true, content: $("<div>", { id: "bottom-right" }) },
    ],
  });

  $().w2layout({
    name: bottomLayoutName,
    panels: [
      { type: "main", overflow: "hidden", hidden: true, resizable: false, content: $("<div>", { id: "prooftree" }) },
      { type: "bottom", overflow: "hidden", resizable: false, content: $("<div>", { id: "progress-bar", height: "100%", style: "background-color: red" }) },
    ],
  });

  const layout = w2ui["layout"];
  const rightLayout = w2ui[rightLayoutName];
  const bottomLayout = w2ui[bottomLayoutName];
  const contextTabs = w2ui[rightLayoutName + "_main_tabs"];
  contextTabs.onClick = function(event: W2UI.W2Event) { $("#myTabsContent").html(event.target); };
  const coqtopTabs = w2ui[rightLayoutName + "_bottom_tabs"];

  const rightLayoutRenderedStream = Rx.Observable
    .create(observer => {
      rightLayout.on({ type: "render", execute: "after" }, () => observer.onNext({}));
    })
    .share();

  layout.content("main", rightLayout);
  layout.content("bottom", bottomLayout);

  const windowResizeStream: Rx.Observable<{}> = Rx.Observable.fromEvent($(window), "resize");
  const layoutResizeStream = setupW2LayoutResizeStream(layout);
  const rightLayoutResizeStream = setupW2LayoutResizeStream(rightLayout);

  return {
    bottomLayout,
    contextTabs,
    layoutResizeStream,
    rightLayout,
    rightLayoutRenderedStream,
    rightLayoutResizeStream,
    windowResizeStream,
  };

}

function setupW2LayoutResizeStream(layout: W2UI.W2Layout): Rx.Observable<{}> {
  return Rx.Observable
    .create(observer => {
      layout.on({ type: "resize", execute: "after" }, () => observer.onNext({}));
    })
    .share()
    ;
}
