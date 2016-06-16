import { ProgressBar } from "../editor/progress-bar";

@component("peacoq-app")

@style(`
:host {
  border: 2px solid red;
}
`)

@template(`<content></content>`)

export class PeaCoqApp extends polymer.Base {
  progressBar: ProgressBar;
  ready() {
    console.log("PeaCoqApp ready");
    this.progressBar = ProgressBar.create<ProgressBar>(42);
    Polymer.dom(this).appendChild(this.progressBar);
  }
  constructor() {
    super();
    console.log("PeaCoqApp constructor");
  }
  attached() {
    console.log("PeaCoqApp attached");
    console.log(this.progressBar.progressField);
  }
}

PeaCoqApp.register();
