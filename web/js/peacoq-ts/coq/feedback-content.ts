import * as SertopUtils from "../sertop/utils";

export function fromCoqtop(f: { tag: string; contents: any }): IFeedbackContent {
  const { tag, contents } = f;
  switch (tag) {
    case "AddedAxiom":
      return new AddedAxiom();
    case "Custom":
      console.log("TODO: FeedbackContent for " + tag, f);
      break;
    case "ErrorMsg":
      const [[start, stop], message] = contents;
      debugger; // does Coqtop expose a full location?
      // return new ErrorMsg([start, stop], replaceNBSPWithSpaces(message));
      break;
    case "FileDependency":
      const [file, dependsOnFile] = contents;
      return new FileDependency(file, dependsOnFile);
    case "FileLoaded":
      let [qualifiedModuleName, path] = contents;
      return new FileLoaded(qualifiedModuleName, path);
    case "GlobDef":
    case "GlobRef":
    case "Goals":
    case "Message":
      debugger;
      break;
    case "Processed":
      return new Processed();
    case "ProcessingIn":
      return new ProcessingIn(contents);
    case "WorkerStatus":
      debugger;
      break;
    // other tags don't need fields
    default:
      throw ("Unknown FeedbackContent tag: " + tag);
  }
  debugger;
  return <any>undefined; // to shut up TypeScript for now
}

export function fromSertop(o): IFeedbackContent {
  if (typeof o === "string") {
    switch (o) {
      case "Processed": return new Processed();
      default: debugger;
    }
  }
  const [name, ...args] = o;
  switch (name) {
    case "ErrorMsg":
      const [coqLocation, message] = args;
      return new ErrorMsg(SertopUtils.coqLocationFromSexp(coqLocation), message);
    case "FileDependency":
      const [depends, file] = args;
      switch (depends.length) {
        case 0: return new FileDependency(nothing(), file);
        case 1: return new FileDependency(just(depends[0]), file);
        default: debugger;
      }
    case "FileLoaded":
      const [qualifiedModuleName, path] = args;
      return new FileLoaded(qualifiedModuleName, path);
    case "Message":
      const [level, ] = args;
      return new Message(level);
    case "ProcessingIn":
      const [branch] = args;
      return new ProcessingIn(branch);
    default: debugger;
  }
  debugger;
  return <any>undefined; // to shut up TypeScript for now
}

export class AddedAxiom implements IFeedbackContent.IAddedAxiom { }

export class ErrorMsg implements IFeedbackContent.IErrorMsg {
  constructor(
    public location: CoqLocation,
    public message: string
  ) {
  }
}

export class FileDependency implements IFeedbackContent.IFileDependency {
  constructor(
    public dependsOnFile: Maybe<string>,
    public file: string
  ) { }
}

export class FileLoaded implements IFeedbackContent.IFileLoaded {
  constructor(
    qualifiedModuleName: string,
      path: string
  ) { }
}

export class Message implements IFeedbackContent.IMessage {
  constructor(
    public level: string
  ) { }
  tostring() { return `Message(${this.level})`; }
}

export class Processed implements IFeedbackContent.IProcessed {
  toString() { return "Processed"; }
}

export class ProcessingIn implements IFeedbackContent.IProcessingIn {
  constructor(
    public branch: string
  ) { }
  toString() {
    return `ProcessingIn(${this.branch})`;
  }
}

export class WorkerStatus implements IFeedbackContent.IWorkerStatus {
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
