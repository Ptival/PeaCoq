export function fromCoqtop(f: { tag: string; contents: any }) {
  const { tag, contents } = f;
  switch (tag) {
    case "AddedAxiom":
      return new AddedAxiom();
    case "Custom":
      console.log("TODO: FeedbackContent for " + tag, f);
      break;
    case "ErrorMsg":
      const [[start, stop], message] = contents;
      return new ErrorMsg([start, stop], replaceNBSPWithSpaces(message));
    case "FileDependency":
      const [file, dependsOnFile] = contents;
      return new FileDependency(file, dependsOnFile);
    case "FileLoaded":
      return new FileLoaded(contents);
    case "GlobDef":
    case "GlobRef":
    case "Goals":
    case "Message":
      console.log("TODO: FeedbackContent for " + tag, f);
      break;
    case "Processed":
      return new Processed();
    case "ProcessingIn":
      return new ProcessingIn(contents);
    case "WorkerStatus":
      console.log("TODO: FeedbackContent for " + tag, f);
      break;
    // other tags don't need fields
    default:
      throw ("Unknown FeedbackContent tag: " + tag);
  }
}

export function fromSertop(o): IFeedbackContent {
  throw "TODO";
}

export class AddedAxiom implements FeedbackContent.IAddedAxiom { }

export class ErrorMsg implements FeedbackContent.IErrorMsg {
  constructor(
    public location: CoqLocation,
    public message: string
  ) {
  }
}

export class FileDependency implements FeedbackContent.IFileDependency {
  constructor(
    public dependsOnFile: string,
    public file: string
  ) { }
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
