export function create(f: { tag: string; contents: Object }) {
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

export class AddedAxiom implements FeedbackContent.IAddedAxiom { }

export class ErrorMsg implements FeedbackContent.IErrorMsg {
  message: string;
  start: number;
  stop: number;
  constructor(c) {
    let [[start, stop], message] = c;
    this.start = start;
    this.stop = stop;
    this.message = replaceNBSPWithSpaces(message);
  }
}

export class FileDependency implements FeedbackContent.IFileDependency {
  dependsOnFile: string;
  file: string;
  constructor(c) {
    let [file, dependsOnFile] = c;
    this.dependsOnFile = dependsOnFile;
    this.file = file;
  }
}

export class FileLoaded implements FeedbackContent.IFileLoaded {
  path: string;
  qualifiedModuleName: string;
  constructor(c) {
    let [qualifiedModuleName, path] = c;
    this.path = path;
    this.qualifiedModuleName = qualifiedModuleName;
  }
}

export class Processed implements FeedbackContent.IProcessed {
  toString() { return "Processed"; }
}

export class ProcessingIn implements FeedbackContent.IProcessingIn {
  s: string;
  constructor(s) {
    this.s = s;
  }
  toString() {
    return `ProcessingIn(${this.s})`;
  }
}

export class WorkerStatus implements FeedbackContent.IWorkerStatus {
  id: string;
  status: string;
  constructor(c) {
    let [id, status] = c;
    this.id = id;
    this.status = status;
  }
  toString() {
    return `WorkerStatus(${this.id}, ${this.status})`;
  }
}
