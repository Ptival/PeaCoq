export class ValueFail {
  stateId: number;
  location: string;
  message: string;
  constructor(v) {
    this.stateId = v[0];
    this.location = v[1];
    this.message = trimSpacesAround(unbsp(v[2]));
  }
}
