
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
//
// let keybindings: KeyBinding[] = [
//   {
//     jQ: "alt+ctrl+l",
//     aceWin: "Alt-Ctrl-L",
//     aceMac: "Option-Command-L",
//     handler: onAltCtrlL,
//   },
//   {
//     jQ: "alt+ctrl+s",
//     aceWin: "Alt-Ctrl-S",
//     aceMac: "Option-Command-S",
//     handler: saveLocal,
//   },
//   {
//     jQ: "alt+ctrl+down",
//     aceWin: "Alt-Ctrl-Down",
//     aceMac: "Option-Command-Down",
//     handler: () => onNext(coqDocument)
//   },
//   {
//     jQ: "alt+ctrl+up",
//     aceWin: "Alt-Ctrl-Up",
//     aceMac: "Option-Command-Down",
//     handler: () => onPrevious(coqDocument)
//   },
//   {
//     jQ: "alt+ctrl+right",
//     aceWin: "Alt-Ctrl-Right",
//     aceMac: "Option-Command-Right",
//     handler: () => onGotoCaret(coqDocument)
//   },
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
  gotoCaret: Rx.Observable<{}>;
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
    gotoCaret: createBindingForKey("right"),
    load: createBindingForKey("l"),
    next: createBindingForKey("down"),
    previous: createBindingForKey("up"),
    save: createBindingForKey("s"),
  };
}
