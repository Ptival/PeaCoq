
export function setup(): void {
  forallInteraction();
}

function addInteraction(selector: string, handler: (e: Element) => void): void {
  $(selector)
    .click(e => {
      e.preventDefault();
      e.stopImmediatePropagation();
      handler(e.target);
    });
}

function forallInteraction(): void {
  addInteraction(".box:contains(∀)", (target) => {
    console.log("click", target);
  });
}
