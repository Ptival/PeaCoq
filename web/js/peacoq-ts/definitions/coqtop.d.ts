
interface ICoqtopInput {
  // this is easier than pattern-matching on the output stream
  callback?: (r: ICoqtopResponse<this, any>) => void;
  // the user might want to attach data that gets copied in the output
  // data: any;
  getArgs(): Object;
  getCmd(): string;
}

interface ICoqtopOutput<I, O> {
  response: ICoqtopResponse<I, O>;
  stateId: number;
  editId: number;
  messages: Object[];
  feedback: Object[];
}

interface ICoqtopResponse<I, O> {
  input: I;
  tag: string;
  contents: O;
}
