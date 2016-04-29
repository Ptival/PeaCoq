export abstract class FeedbackContent {
  static create(f: { tag: string; contents: Object }) {
    switch (f.tag) {
      case "AddedAxiom":
        return new AddedAxiom();
      case "Custom":
        console.log("TODO: FeedbackContent for " + f.tag, f);
        break;
      case "ErrorMsg":
        return new ErrorMsg(f.contents);
      case "FileDependency":
        return new FileDependency(f.contents);
      case "FileLoaded":
        return new FileLoaded(f.contents);
      case "GlobDef":
      case "GlobRef":
      case "Goals":
      case "Message":
        console.log("TODO: FeedbackContent for " + f.tag, f);
        break;
      case "Processed":
        return new Processed();
      case "ProcessingIn":
        return new ProcessingIn(f.contents);
      case "WorkerStatus":
        console.log("TODO: FeedbackContent for " + f.tag, f);
        break;
      // other tags don't need fields
      default:
        throw ("Unknown FeedbackContent tag: " + f.tag);
    }
  }
}

export class AddedAxiom extends FeedbackContent { }

export class ErrorMsg extends FeedbackContent {
  message: string;
  start: number;
  stop: number;
  constructor(c) {
    super();
    let [[start, stop], message] = c;
    this.start = start;
    this.stop = stop;
    this.message = replaceNBSPWithSpaces(message);
  }
}

export class FileDependency extends FeedbackContent {
  dependsOnFile: string;
  file: string;
  constructor(c) {
    super();
    let [file, dependsOnFile] = c;
    this.dependsOnFile = dependsOnFile;
    this.file = file;
  }
}

export class FileLoaded extends FeedbackContent {
  path: string;
  qualifiedModuleName: string;
  constructor(c) {
    super();
    let [qualifiedModuleName, path] = c;
    this.path = path;
    this.qualifiedModuleName = qualifiedModuleName;
  }
}

export class Processed extends FeedbackContent {
  toString() { return "Processed"; }
}

export class ProcessingIn extends FeedbackContent {
  s: string;
  constructor(s) {
    super();
    this.s = s;
  }
  toString() {
    return "ProcessingIn(" + this.s + ")";
  }
}
