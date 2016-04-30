
interface ICoqtopInput {
  // this is easier than pattern-matching on the output stream
  callback: (r: ICoqtopResponse) => void;
  // the user might want to attach data that gets copied in the output
  // data: any;
  getArgs(): Object;
  getCmd(): string;
}

interface ICoqtopOutput {
  response: ICoqtopResponse;
  stateId: number;
  editId: number;
  messages: Object[];
  feedback: Object[];
}

interface ICoqtopResponse {
  input: ICoqtopInput;
  tag: string;
  contents: any;
}
