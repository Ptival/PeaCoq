// FIXME: this file should not exist anymore, remove all definitions

type GlobLevel = IGlobSortGen<LevelInfo>
type GlobSort = IGlobSortGen<SortInfo>
type InstanceExpr = Array<GlobLevel>
type LevelInfo = Maybe<string>
type SortInfo = string[]

interface AddReturn {
    stateId: number
    eitherNullStateId: number
    output: string
}

interface IGlobSortGen<T> { }

interface IGoal {
    goalId: number
    goalHyp: string[]
    goalCcl: string
}

interface BeforeAfter<T> {
    before: T[]
    after: T[]
}

interface IGoals<T> {
    fgGoals: T[]
    bgGoals: BeforeAfter<T>[]
    shelvedGoals: T[]
    givenUpGoals: T[]
}

interface IMessage {
    content: string
    level: IMessageLevel
    // display(): void
}

interface IMessageLevel {
}

interface IStatus {
    // statusPath: string[]
    statusProofName: string
    statusAllProofs: string
    // statusProofNum: number
}

interface ErrorLocation {
    startPos: number
    stopPos: number
}

interface IValueFail {
    location: Maybe<ErrorLocation>
    message: string
    stateId: number
}
