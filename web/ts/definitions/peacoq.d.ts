// input
type Command$ = Rx.Observable<import('../sertop/serapi-protocol').Cmd>

type StmAdd$     = Rx.Observable<import('../sertop/serapi-protocol').Add>
type StmCancel$  = Rx.Observable<import('../sertop/serapi-protocol').Cancel>
type StmQuery$   = Rx.Observable<import('../sertop/serapi-protocol').Query>

// output
type Answer$<T> = Rx.Observable<import('../sertop/answer').Answer.Answer<T>>

type Ack$       = Answer$<import('../sertop/answer-kind').Ack>
type Completed$ = Answer$<import('../sertop/answer-kind').Completed>
type Added$     = Answer$<import('../sertop/answer-kind').Added>
type Canceled$  = Answer$<import('../sertop/answer-kind').Canceled>
type ObjList$   = Answer$<import('../sertop/answer-kind').ObjList>
type CoqExn$    = Answer$<import('../sertop/answer-kind').CoqExn>

// feedback

type Feedback$<T> = Rx.Observable<import('../coq/lib/feedback').Feedback<T>>

type Processed$  = Feedback$<import('../coq/lib/feedback').Processed>
type Message$<L> = Feedback$<import('../coq/lib/feedback').Message<L>>

type Debug$   = Message$<import('../coq/lib/feedback').Debug>
type Error$   = Message$<import('../coq/lib/feedback').Error>
type Info$    = Message$<import('../coq/lib/feedback').Info>
type Notice$  = Message$<import('../coq/lib/feedback').Notice>
type Warning$ = Message$<import('../coq/lib/feedback').Warning>

interface PeaCoqContextElement {
    goal: IGoal
    ppgoal: IPeaCoqGoal
}

type PeaCoqContext = IGoals<PeaCoqContextElement>

type ConstrExpr = import('../coq/lib/c-ast').cAST<import('../coq/intf/constr-expr').ConstrExprR>

interface IPeaCoqGoal {
    hyps : PeaCoqHyp[]
    concl : ConstrExpr
    getHTML() : JQuery
}

interface PeaCoqHyp {
    name : string
    maybeTerm : Maybe<ConstrExpr>
    type : ConstrExpr
}
