
/*
I can't seem to make Ace properly bubble key events, or when they bubble,
jQuery somehow does not recognize them. So fuck it, keybindings are added
to both the page and each editor...
*/
// type KeyBinding = {
//   jQ: string
//   aceWin: string
//   aceMac: string
//   handler: () => void
// }
//   {
//     jQ: "alt+ctrl+=",
//     aceWin: "Alt-Ctrl-=",
//     aceMac: "Option-Command-=",
//     handler: () => fontIncrease(coqDocument),
//   },
//   {
//     jQ: "alt+ctrl+-",
//     aceWin: "Alt-Ctrl--",
//     aceMac: "Option-Command--",
//     handler: () => fontDecrease(coqDocument),
//   },
// ]

const jQueryPrefix = "alt+ctrl+"
const aceWindowsPrefix = "Alt-Ctrl-"
const aceMacPrefix = "Option-Command-"

function createBindingForKey(
  // doc: ICoqDocument,
  key: string
): Rx.Observable<{}> {
  return Rx.Observable
    .create(observer => {
      $(document).bind("keydown", jQueryPrefix + key, () => observer.onNext({}))
      // TODO: should probably add shortcuts to all Ace editors
      // since they don't bubble up :(
      // doc.editor.commands.addCommand({
      //   name: key,
      //   bindKey: { win: aceWindowsPrefix + key, mac: aceMacPrefix + key },
      //   exec: () => observer.onNext({}),
      // })
    })
    .share()

}

export function setup(): ShortcutsStreams {
  return {
    fontDecrease: createBindingForKey("-"),
    fontIncrease: createBindingForKey("="),
    goToCaret: createBindingForKey("right"),
    load: createBindingForKey("l"),
    next: createBindingForKey("down"),
    previous: createBindingForKey("up"),
    save: createBindingForKey("s"),
  }
}
