interface IKeyBindings {
  public bindings: KeyBinding[]
  public getStreams(): KeyBinding$s
}

interface KeyBinding {
  key: string
  binding: () => void
}

interface KeyBinding$s {
  load$: Rx.Observable<{}>
  next$: Rx.Observable<{}>
}
