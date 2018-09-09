export type CaseStyle
    = LetStyle
    | IfStyle
    | LetPatternStyle
    | MatchStyle
    | RegularStyle

export class LetStyle        { private tag : 'LetStyle' }
export class IfStyle         { private tag : 'IfStyle' }
export class LetPatternStyle { private tag : 'LetPatternStyle' }
export class MatchStyle      { private tag : 'MatchStyle' }
export class RegularStyle    { private tag : 'RegularStyle' }
