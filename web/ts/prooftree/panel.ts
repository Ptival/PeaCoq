// OMG this is so ugly, will fix!!!

// TODO: use an AsyncSubject instead?
export function show(bottomLayout: W2UI.W2Layout): Promise<{}> {
  return new Promise(onFulfilled => {
    const handler = fix(handler => (event: W2UI.W2Event) => {
      event.onComplete = onFulfilled
      bottomLayout.off("show", handler)
    })
    bottomLayout.on("show", handler)
    // layout.set("bottom", { size: "60%" })
    bottomLayout.show("main")
  })
}

export function hide(bottomLayout: W2UI.W2Layout): void {
  // debugger
  // layout.set("bottom", { size: "20px" })
  bottomLayout.hide("main")
}
