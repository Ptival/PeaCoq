import * as FeedbackContent from './feedback-content'

export class Feedback implements IFeedback<IFeedbackContent> {
    constructor(
        public editOrState : EditOrState,
        public editOrStateId : EditId | StateId,
        public feedbackContent : IFeedbackContent,
        public routeId : RouteId
    ) {
    }
    public toString() {
        return (
            'Feedback(' + this.editOrState + ', ' + this.editOrStateId + ', ' +
                this.feedbackContent + ', ' + this.routeId + ')'
        )
    }
}

// export function fromCoqtop(f) {
//   const [{ tag : es, contents : esid }, fc, rid] = f
//   const editOrState
//   switch (es) {
//     case 'edit' : editOrState = EditOrState.Edit
//       break
//     case 'state' : editOrState = EditOrState.State
//       break
//     default : throw 'coqtopMkFeedback : neither edit nor state'
//   }
//   return new Feedback(editOrState, esid, FeedbackContent.fromCoqtop(fc), rid)
// }

export function fromSertop(
    f : [any, [[any, [string, string]], [any, string], [any, string]]]
) {
    //const [, [[, [es, esid]], [, fc], [, rid]]] = f
    const [, [ [, docId], [,spanId], [,route], [,contents] ]] = f
    let editOrState : EditOrState
    switch (es) {
        case 'Edit' :
            editOrState = EditOrState.Edit
            break
        case 'State' :
            editOrState = EditOrState.State
            break
        default :
            debugger
            // throw 'coqtopMkFeedback: neither edit nor state'
            editOrState = EditOrState.State
    }
    return new Feedback(editOrState, +esid, FeedbackContent.fromSertop(fc), +rid)
}
