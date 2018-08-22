import * as _ from 'lodash'

/*
Note: this is not the way this should work in the end, as it is pretty brittle,
but this is for the sake of demonstrating this kind of feature easily.
*/

export function setup() : void {
  $.contextMenu('destroy')
  equalsInteraction()
  forallInteraction()
}

function addInteraction(
  targetBox : Element,
  items : (trigger : JQuery) => any
) : void {
  // we use the special form to prevent menu from popping-up when clicking
  // sub-elements
  $.contextMenu({
    selector : '.box',
    trigger : 'left',
    build : ($trigger, event) => {
      if (!event.target) { return false }
      const closestBox = $(event.target).closest('.box')[0]
      // prevent the menu if the clicked element is in a sub-box of the wanted one
      if (closestBox !== targetBox) { return false }
      return { items : items($trigger) }
    }
  })
}

function equalsInteraction() : void {
  addInteraction(
    $('.tag-notation')
      .filter((n, e) => $(e).text().includes('='))
      .closest('.box')[0],
    $trigger => ({
      reflexivity : {
        name : 'reflexivity.',
        callback : () => { console.log('reflexivity.') }
      },
    })
  )
}

function forallInteraction() : void {
  addInteraction(
    $('.tag-keyword')
      .filter((n, e) => $(e).text().includes('∀'))
      .closest('.box')[0],
    $trigger => {
      const result = {}
      Rx.Observable
        //     0         1         2        3
        // <forall> (a b : ...) (c : ...) <body>
        .fromArray($trigger.children().slice(1, -1).toArray())
        // 0 1      2
        // a b : <type>
        .flatMap(a => $(a).children().slice(0, -1).toArray())
        .map(e => $(e).text())
        .toArray()
        .subscribe(a => {
          _(prefixes(a))
            .reverse()
            .each(prefix => {
              const s = `intros ${prefix.join(' ')}.`
              result[s] = { name : s, callback : () => { console.log(s) }}
            })
        })
      return result
  })
}
