
/*
I can't seem to make Ace properly bubble key events, or when they bubble,
jQuery somehow does not recognize them. So fuck it, keybindings are added
to both the page and each editor...
*/
// type KeyBinding = {
//   jQ: string;
//   aceWin: string;
//   aceMac: string;
//   handler: () => void
// };
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
// ];

let jQueryPrefix = "alt+ctrl+";
let aceWindowsPrefix = "Alt-Ctrl-";
let aceMacPrefix = "Option-Command-";

interface ShortcutsStreams {
  fontIncrease: Rx.Observable<{}>;
  fontDecrease: Rx.Observable<{}>;
  goToCaret: Rx.Observable<{}>;
  load: Rx.Observable<{}>;
  next: Rx.Observable<{}>;
  previous: Rx.Observable<{}>;
  save: Rx.Observable<{}>;
}

function createBindingForKey(key: string): Rx.Observable<{}> {
  return Rx.Observable
    .create((observer) => {
      $(document).bind("keydown", jQueryPrefix + key, () => observer.onNext({}));
      // TODO: should probably add shortcuts to all Ace editors
      // since they don't bubble up :(
      coqDocument.editor.commands.addCommand({
        name: key,
        bindKey: { win: aceWindowsPrefix + key, mac: aceMacPrefix + key },
        exec: () => observer.onNext({}),
      });
    })
    .share()
    ;
}

function setupKeybindings(): ShortcutsStreams {
  return {
    fontDecrease: createBindingForKey("-"),
    fontIncrease: createBindingForKey("="),
    goToCaret: createBindingForKey("right"),
    load: createBindingForKey("l"),
    next: createBindingForKey("down"),
    previous: createBindingForKey("up"),
    save: createBindingForKey("s"),
  };
}
