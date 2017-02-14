export class KeyBindings implements IKeyBindings {
  public bindings: KeyBinding[]
  // private fontDecrease: Rx.Subject<{}>
  // private fontIncrease: Rx.Subject<{}>
  // private goToCaret: Rx.Subject<{}>
  private load: Rx.Subject<{}>
  private next: Rx.Subject<{}>
  // private previous: Rx.Subject<{}>
  // private save: Rx.Subject<{}>

  constructor() {
    this.load = new Rx.Subject<{}>()
    this.next = new Rx.Subject<{}>()
    this.bindings = [
      { key: "down", binding: () => this.onDown() }, // seems broken on CodeMirror
      { key: "l", binding: () => this.onL() },
      { key: "n", binding: () => this.onDown() },
    ]
    this.bindings.forEach(({ key, binding }) => {
      $(document).bind("keydown", jQueryPrefix + key, binding)
    })
  }

  public getStreams(): KeyBinding$s {
    return {
      // fontDecrease$: createBindingForKey("-"),
      // fontIncrease$: createBindingForKey("="),
      // goToCaret$: createBindingForKey("right"),
      load$: this.load.asObservable(),
      next$: this.next.asObservable(),
      // previous$: createBindingForKey("up"),
      // save$: createBindingForKey("s"),
    }
  }

  public onDown() { this.next.onNext({}) }
  public onL() { this.load.onNext({}) }
}

const jQueryPrefix = "alt+ctrl+"
// const aceWindowsPrefix = "Alt-Ctrl-"
// const aceMacPrefix = "Option-Command-"
const codeMirrorPrefix = "Ctrl-Alt-"

// function createBindingForKey(
//   // doc: ICoqDocument,
//   key: string
// ): Rx.Subject<{}> {
//   return Rx.Subject
//     .create(observer => {
//       $(document).bind("keydown", jQueryPrefix + key, () => observer.onNext({}))
//       // TODO: should probably add shortcuts to all Ace editors
//       // since they don't bubble up :(
//       // doc.editor.commands.addCommand({
//       //   name: key,
//       //   bindKey: { win: aceWindowsPrefix + key, mac: aceMacPrefix + key },
//       //   exec: () => observer.onNext({}),
//       // })
//     })
//     .share()

// }

// export function setup(): ShortcutsStreams {
//   return {
//     fontDecrease: createBindingForKey("-"),
//     fontIncrease: createBindingForKey("="),
//     goToCaret: createBindingForKey("right"),
//     load: createBindingForKey("l"),
//     next: createBindingForKey("down"),
//     previous: createBindingForKey("up"),
//     save: createBindingForKey("s"),
//   }
// }
