
interface ICoqtopInput {
  // this is easier than pattern-matching on the output stream
  callback?: (r: ICoqtopOutput<this, any>) => void;
  // the user might want to attach data that gets copied in the output
  // data: any;
  getArgs(): Object;
  getCmd(): string;
}

interface ICoqtopOutput<I, O> {
  input: I;
  output: any; //IAnswer;
}

interface ICoqtopResponse<O> {
  tag: string;
  contents: O;
}
