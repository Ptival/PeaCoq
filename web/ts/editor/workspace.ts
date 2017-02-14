import { create as createEditor } from "./editor"

export class Workspace {
  private context: IEditor
  private editor: IEditor
  constructor(
    private toplevel: IToplevel
  ) {
    this.editor = createEditor("editor")
    this.context = createEditor("context")
  }
}
