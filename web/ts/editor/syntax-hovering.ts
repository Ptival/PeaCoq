export function setup() {
  $(document)
    .on("mouseenter mouseover", ".syntax", function (e) {
      $(this).toggleClass("peacoq-highlight", true)
      e.stopImmediatePropagation()
    })
    .on("mouseout mouseleave", ".syntax", function (e) {
      $(this).toggleClass("peacoq-highlight", false)
      e.stopImmediatePropagation()
    })
}
