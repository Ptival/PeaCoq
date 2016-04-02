import { MessageLevel, mkMessageLevel } from "./message-level";

export class Message {
  level: MessageLevel;
  content: string;
  constructor(m) {
    this.level = mkMessageLevel(m[0]);
    this.content = unbsp(m[1]);
  }
  display() {
    let tab = this.level.getAssociatedTab();
    tab.setValue(this.content, false);
  }
  toString() {
    return (
      "[" + this.level.toString() + "]\n" + this.content
    );
  }
}
