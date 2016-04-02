import { FeedbackContent } from "./feedback-content";

export class Feedback {
  // TODO: give this a less lame type
  editOrState: string;
  editOrStateId: number;
  feedbackContent: FeedbackContent;
  routeId: number;
  constructor(f) {
    switch (f[0].tag) {
      case "State":
        this.editOrState = "state";
        break;
      case "Edit":
        this.editOrState = "edit";
        break;
      default:
        throw "Feedback tag was neither State nor Edit";
    };
    this.editOrStateId = f[0].contents;
    this.feedbackContent = FeedbackContent.create(f[1]);
    this.routeId = f[2];
  }
  toString() {
    return (
      "Feedback(" + this.editOrState + ", " + this.editOrStateId + ", " +
      this.feedbackContent + ", " + this.routeId + ")"
    );
  }
}
