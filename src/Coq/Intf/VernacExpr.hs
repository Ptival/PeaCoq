module Coq.Intf.VernacExpr where

import Coq.Intf.DeclKinds
import Coq.Intf.MiscTypes
import Coq.Kernel.Names
import Coq.Lib.Canary
import Coq.Lib.Loc
import Coq.Library.LibNames
import OCaml

type LIdent = Located Id
type LName = Located Name
type LString = Located String
type LReference = Reference

data ClassRawExpr
  = FunClass
  | SortClass
  | RefClass (OrByNotation Reference)
  deriving (Show)

data GoalSelector
  = SelectNth Int
  | SelectId Id
  | SelectAll
  | SelectAllParallel
  deriving (Show)

type GoaLIdentifier = String
type ScopeName = String

data GoalReference
  = OpenSubgoals
  | NthGoal Int
  | GoalId GoaLIdentifier
  deriving (Show)

data Printable
  = PrintTables
  | PrintFullContext
  | PrintSectionContext Reference
  | PrintInspect Int
  | PrintGrammar String
  | PrintLoadPath (Maybe DirPath)
  | PrintModules
  | PrintModule Reference
  | PrintModuleType Reference
  | PrintNamespace DirPath
  | PrintMLLoadPath
  | PrintMLModules
  | PrintDebugGC
  | PrintName (OrByNotation Reference)
  | PrintGraph
  | PrintClasses
  | PrintTypeClasses
  | PrintInstances (OrByNotation Reference)
  | PrintLtac Reference
  | PrintCoercions
  | PrintCoercionPaths ClassRawExpr ClassRawExpr
  | PrintCanonicalConversions
  | PrintUniverses Bool (Maybe String)
  | PrintHint (OrByNotation Reference)
  | PrintHintGoal
  | PrintHintDbName String
  | PrintRewriteHintDbName String
  | PrintHintDb
  | PrintScopes
  | PrintScope String
  | PrintVisibility (Maybe String)
  | PrintAbout (OrByNotation Reference) (Maybe Int)
  | PrintImplicit (OrByNotation Reference)
  | PrintAssumptions Bool Bool (OrByNotation Reference)
  | PrintStrategy (Maybe (OrByNotation Reference))

data SearchAboutItem
  = SearchSubPattern ConstrPatternExpr
  | SearchString String (Maybe ScopeName)

data Searchable
  = SearchPattern ConstrPatternExpr
  | SearchRewrite ConstrPatternExpr
  | SearchHead ConstrPatternExpr
  | SearchAbout [(Bool, SearchAboutItem)]

data Locatable
  = LocateAny (OrByNotation Reference)
  | LocateTerm (OrByNotation Reference)
  | LocateLibrary Reference
  | LocateModule Reference
  | LocateTactic Reference
  | LocateFile String

data Showable
  = ShowGoal GoalReference
  | ShowGoalImplicitly (Maybe Int)
  | ShowProof
  | ShowNode
  | ShowScript
  | ShowExistentials
  | ShowUniverses
  | ShowTree
  | ShowProofNames
  | ShowIntros Bool
  | ShowMatch LIdent
  | ShowThesis

data Comment
  = CommentConstr ConstrExpr
  | CommentString String
  | CommentInt Int

data ReferenceOrConstr
  = HintsReference Reference
  | HintsConstr ConstrExpr

data HintsExpr
  = HintsResolve [(Maybe Int, Bool, ReferenceOrConstr)]
  | HintsImmediate [ReferenceOrConstr]
  | HintsUnfold [Reference]
  | HintsTransparency [Reference] Bool
  | HintsMode Reference [Bool]
  | HintsConstructors [Reference]
  | HintsExtern Int (Maybe ConstrExpr) RawTacticExpr

data SearchRestriction
  = SearchInside [Reference]
  | SearchOutside [Reference]

type RecFlag = Bool
type VerboseFlag = Bool
data OpacityFlag
  = Opaque (Maybe [LIdent])
  | Transparent
  deriving (Show)
type CoercionFlag = Bool
type InstanceFlag = Maybe Bool
type ExportFlag = Bool
type InductiveFlag = RecursivityKind
type OnlyParsingFlag = Maybe CompatVersion
type LocalityFlag = Bool
type ObsoleteLocality = Bool

data OptionValue
  = BoolValue Bool
  | IntValue (Maybe Int)
  | StringValue String
  deriving (Show)

data OptionRefValue
  = StringRefValue String
  | QualidRefValue Reference
  deriving (Show)

type SortExpr = GlobSort

data DefinitionExpr
  = ProveBody [LocalBinder] ConstrExpr
  | DefineBody [LocalBinder] (Maybe RawRedExpr) ConstrExpr (Maybe ConstrExpr)

type FixpointExpr =
  (
    Located Id,
    (Maybe (Located Id), RecursionOrderExpr),
    [LocalBinder],
    ConstrExpr,
    Maybe ConstrExpr
  )

type CoFixpointExpr =
    (
      Located Id,
      [LocalBinder],
      ConstrExpr,
      Maybe ConstrExpr
    )

data LocalDeclExpr
  = AssumExpr LName ConstrExpr
  | DefExpr LName ConstrExpr (Maybe ConstrExpr)
  deriving (Show)

data InductiveKind
  = Inductive_kw
  | CoInductive
  | Variant
  | Record
  | Structure
  | Class Bool
  deriving (Show)
type DeclNotation = (LString, ConstrExpr, Maybe ScopeName)
type SimpleBinder = ([LIdent], ConstrExpr)
type ClassBinder = (LIdent, [ConstrExpr])
type WithCoercion a = (CoercionFlag, a)
type WithInstance a = (InstanceFlag, a)
type WithNotation a = (a , [DeclNotation])
type WithPriority a = (a, Maybe Int)
type ConstructorExpr = WithCoercion (LIdent, ConstrExpr)
data ConstructorListOrRecordDeclExpr
  = Constructors [ConstructorExpr]
  | RecordDecl (Maybe LIdent) [WithNotation (WithPriority (WithInstance LocalDeclExpr))]
  deriving (Show)
type InductiveExpr =
  (
    WithCoercion LIdent,
    [LocalBinder],
    Maybe ConstrExpr,
    InductiveKind,
    ConstructorListOrRecordDeclExpr
  )

type OneInductiveExpr = (LIdent, [LocalBinder], Maybe ConstrExpr, [ConstructorExpr])

data GrammarTacticProdItemExpr
  = TacTerm String
  | TacNonTerm Loc String (Maybe (NamesId, String))
  deriving (Show)

data SyntaxModifier
  = SetItemLevel [String] ProductionLevel
  | SetLevel Int
  | SetAssoc GramAssoc
  | SetEntryType String SimpleConstrProdEntryKey
  | SetOnlyParsing CompatVersion
  | SetFormat String (Located String)
  deriving (Show)

data ProofEnd
  = Admitted
  | Proved OpacityFlag (Maybe (LIdent, Maybe TheoremKind))
  deriving (Show)

data Scheme
  = InductionScheme Bool (OrByNotation Reference) SortExpr
  | CaseScheme Bool (OrByNotation Reference) SortExpr
  | EqualityScheme (OrByNotation Reference)
  deriving (Show)

data SectionSubsetExpr
  = SsSet [LIdent]
  | SsCompl SectionSubsetExpr
  | SsUnion SectionSubsetExpr SectionSubsetExpr
  | SsSubstr SectionSubsetExpr SectionSubsetExpr
  deriving (Show)

data SectionSubsetDescr
  = SsAll
  | SsType
  | SsExpr SectionSubsetExpr
  deriving (Show)

type ExtendName = (String, Int)

data RegisterKind
  = RegisterInline
  deriving (Show)

data Bullet
  = Dash Int
  | Star Int
  | Plus Int
  deriving (Show)

data STMVernac a
  = JoinDocument
  | Finish
  | Wait
  | PrintDag
  | Observe StateId
  | Command a
  | PGLast a
  deriving (Show)

data ModuleSignature a
  = Enforce a
  | Check [a]
  deriving (Show)

data Inline
  = NoInline
  | DefaultInline
  | InlineAt Int
  deriving (Show)

type ModuleASTInl = (ModuleAST, Inline)
type ModuleBinder = (Maybe Bool, [LIdent], ModuleASTInl)

data VernacExpr
  {- Control -}
  = VernacLoad VerboseFlag String
  | VernacTime VernacList
  | VernacRedirect String VernacList
  | VernacTimeout Int VernacExpr
  | VernacFail VernacExpr
  | VernacError Exn
    {- Syntax -}
  | VernacTacticNotation Int [GrammarTacticProdItemExpr] RawTacticExpr
  | VernacSyntaxExtension ObsoleteLocality LString [SyntaxModifier]
  | VernacOpenCloseScope ObsoleteLocality Bool ScopeName
  | VernacDelimiters ScopeName (Maybe String)
  | VernacBindScope ScopeName [OrByNotation Reference]
  | VernacInfix ObsoleteLocality (LString, [SyntaxModifier]) ConstrExpr (Maybe ScopeName)
  | VernacNotation ObsoleteLocality ConstrExpr (LString, [SyntaxModifier]) (Maybe ScopeName)
  | VernacNotationAddFormat String String String
    {- Gallina -}
  | VernacDefinition (Maybe Locality, DefinitionObjectKind) LIdent DefinitionExpr
  | VernacStartTheoremProof TheoremKind [(Maybe LIdent, ([LocalBinder], ConstrExpr, Maybe (Maybe LIdent, RecursionOrderExpr)))] Bool
  | VernacEndProof ProofEnd
  | VernacExactProof ConstrExpr
  | VernacAssumption (Maybe Locality, AssumptionObjectKind) Inline [WithCoercion SimpleBinder]
  | VernacInductive PrivateFlag InductiveFlag [(InductiveExpr, [DeclNotation])]
  | VernacFixpoint (Maybe Locality) [(FixpointExpr, [DeclNotation])]
  | VernacCoFixpoint (Maybe Locality) [(CoFixpointExpr, [DeclNotation])]
  | VernacScheme [(Maybe LIdent, Scheme)]
  | VernacCombinedScheme LIdent [LIdent]
  | VernacUniverse [LIdent]
  | VernacConstraint [(LIdent, ConstraintType, LIdent)]
    {- Gallina extensions -}
  | VernacBeginSection LIdent
  | VernacEndSegment LIdent
  | VernacRequire (Maybe LReference) (Maybe ExportFlag) [LReference]
  | VernacImport ExportFlag [LReference]
  | VernacCanonical (OrByNotation Reference)
  | VernacCoercion ObsoleteLocality (OrByNotation Reference) ClassRawExpr ClassRawExpr
  | VernacNameSectionHypSet LIdent SectionSubsetDescr
    {- Type classes -}
  | VernacInstance Bool [LocalBinder] TypeClassConstraint (Maybe (Bool, ConstrExpr)) (Maybe Int)
  | VernacContext [LocalBinder]
  | VernacDeclareInstances [Reference] (Maybe Int)
  | VernacDeclareClass Reference
    {- Modules and Module Types -}
  | VernacDeclareModule (Maybe Bool) LIdent [ModuleBinder] ModuleASTInl
  | VernacDefineModule (Maybe Bool) LIdent [ModuleBinder] (ModuleSignature ModuleASTInl) [ModuleASTInl]
  | VernacDeclareModuleType LIdent [ModuleBinder] [ModuleASTInl] [ModuleASTInl]
  | VernacInclude [ModuleASTInl]
    {- Solving -}
  | VernacSolve GoalSelector (Maybe Int) RawTacticExpr Bool
  | VernacSolveExistential Int ConstrExpr
    {- Auxiliary file and library management -}
  | VernacAddLoadPath RecFlag String (Maybe DirPath)
  | VernacRemoveLoadPath String
  | VernacAddMLPath RecFlag String
  | VernacDeclareMLModule [String]
  | VernacChdir (Maybe String)
    {- State management -}
  | VernacWriteState String
  | VernacRestoreState String
    {- Resetting -}
  | VernacResetName LIdent
  | VernacResetInitial
  | VernacBack Int
  | VernacBackTo Int
    {- Commands -}
  | VernacDeclareTacticDefinition RecFlag [(Reference, Bool, RawTacticExpr)]
  | VernacCreateHintDb String Bool
  | VernacRemoveHints [String] [Reference]
  | VernacHints ObsoleteLocality [String] HintsExpr
  | VernacSyntacticDefinition (Located Id) ([Id], ConstrExpr) ObsoleteLocality OnlyParsingFlag
  | VernacDeclareImplicits (OrByNotation Reference) [[(Explicitation, Bool, Bool)]]
  | VernacArguments (OrByNotation Reference) [[(Name, Bool, Maybe (Loc, String), Bool, Bool)]] Int [Flag]
  | VernacArgumentsScope (OrByNotation Reference) [Maybe ScopeName]
  | VernacReserve [SimpleBinder]
  | VernacGeneralizable (Maybe [LIdent])
  | VernacSetOpacity (Level, [OrByNotation Reference])
  | VernacSetStrategy [(Level, [OrByNotation Reference])]
  | VernacUnsetOption OptionName
  | VernacSetOption OptionName OptionValue
  | VernacAddOption OptionName [OptionRefValue]
  | VernacRemoveOption OptionName [OptionRefValue]
  | VernacMemOption OptionName [OptionRefValue]
  | VernacPrintOption OptionName
  | VernacCheckMayEval (Maybe RawRedExpr) (Maybe Int) ConstrExpr
  | VernacGlobalCheck ConstrExpr
  | VernacDeclareReduction String RawRedExpr
  | VernacPrint Printable
  | VernacSearch Searchable (Maybe Int) SearchRestriction
  | VernacLocate Locatable
  | VernacRegister LIdent RegisterKind
  | VernacComments [Comment]
  | VernacNop
    {- STM backdoor -}
  | VernacSTM (STMVernac VernacExpr)
    {- Proof management -}
  | VernacGoal ConstrExpr
  | VernacAbort (Maybe LIdent)
  | VernacAbortAll
  | VernacRestart
  | VernacUndo Int
  | VernacUndoTo Int
  | VernacBacktrack Int Int Int
  | VernacFocus (Maybe Int)
  | VernacUnfocus
  | VernacUnfocused
  | VernacBullet Bullet
  | VernacSubproof (Maybe Int)
  | VernacEndSubproof
  | VernacShow Showable
  | VernacCheckGuard
  | VernacProof (Maybe RawTacticExpr) (Maybe SectionSubsetDescr)
  | VernacProofMode String
    {- Toplevel control -}
  | VernacToplevelControl Exn
    {- For extension -}
  | VernacExtend ExtendName [RawGenericArgument]
    {- Flags -}
  | VernacProgram VernacExpr
  | VernacPolymorphic Bool VernacExpr
  | VernacLocal Bool VernacExpr

type VernacList = [LocatedVernacExpr]

type LocatedVernacExpr = (Loc, VernacExpr)

data Flag
  = ReductionDontExposeCase
  | ReductionNeverUnfold
  | Rename
  | ExtraScopes
  | Assert
  | ClearImplicits
  | ClearScopes
  | DefaultImplicits
  deriving (Show)

data VernacType
  = VTStartProof VernacStart
  | VTSidEff VernacSidEffType
  | VTQED VernacQEDType
  | VTProofStep Bool
  | VTProofMode String
  | VTQuery VernacPartOfScript ReportWith
  | VTSTM VernacControl VernacPartOfScript
  | VTUnknown
  deriving (Show)

type ReportWith = (StateId, RouteId)

data VernacQEDType
  = VTKeep
  | VTKeepAsAxiom
  | VTDrop
  deriving (Show)

type VernacStart = (String, OpacityGuarantee, [Id])
type VernacSidEffType = [Id]
type VernacIsAlias = Bool
type VernacPartOfScript = Bool

data VernacControl
  = VTFinish
  | VTWait
  | VTJoinDocument
  | VTPrintDag
  | VTObserve StateId
  | VTBack StateId
  | VTPG
  deriving (Show)

data OpacityGuarantee
  = GuaranteesOpacity
  | Doesn'tGuaranteeOpacity
  deriving (Show)

data VernacWhen
  = VtNow
  | VtLater
  deriving (Show)

type VernacClassification = (VernacType, VernacWhen)
