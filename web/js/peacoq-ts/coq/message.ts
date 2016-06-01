import { mkMessageLevel } from "./message-level";

export class Message implements IMessage {
  content: string;
  level: IMessageLevel;
  constructor(m) {
    this.level = mkMessageLevel(m[0]);
    this.content = unbsp(m[1]);
  }
  // display(): void {
  //   let tab = this.level.getAssociatedTab();
  //   tab.setValue(this.content, false);
  // }
  toString(): string {
    return (
      "[" + this.level.toString() + "]\n" + this.content
    );
  }
}
