import { Editor } from "./editor"
import { SentenceArray } from "./sentence-array"

export class Buffer extends Editor implements IBuffer {
  public sentences: ISentenceArray

  constructor(
    containerName: string,
    keybindings: IKeyBindings
  ) {
    super(containerName, keybindings)
    this.sentences = new SentenceArray() // (this)
  }

  public getLastSentenceEnd(): IPosition {
    return thisShouldNotHappen()
  }
}
