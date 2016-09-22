export function setup() {
  $(document)
    .on("mouseenter mouseover", ".syntax", (e, ...args) => {
      $(e.currentTarget).toggleClass("peacoq-highlight", true)
      e.stopImmediatePropagation()
    })
    .on("mouseout mouseleave", ".syntax", (e) => {
      $(e.currentTarget).toggleClass("peacoq-highlight", false)
      e.stopImmediatePropagation()
    })
}
