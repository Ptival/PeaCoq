module Coq.Intf.TacExpr where

import Coq.Intf.Locus
import Coq.Intf.MiscTypes
import Coq.Kernel.Names
import Coq.Lib.Loc

type DirectionFlag = Bool

data LazyFlag
  = General
  | Select
  | Once
  deriving (Show)

data GlobalFlag
  = TacGlobal
  | TacLocal
  deriving (Show)

type EvarsFlag = Bool
type RecFlag = Bool
type AdvancedFlag = Bool
type LetInFlag = Bool
type ClearFlag = Maybe Bool

data Debug
  = Debug
  | Info
  | Off
  deriving (Show)

data CoreInductionArg a
  = ElimOnConstr a
  | ElimOnIndent (Located Id)
  | ElimOnAnonHyp Int
  deriving (Show)

type InductionArg a = (ClearFlag, CoreInductionArg a)

data InversionKind
  = SimpleInversion
  | FullInversion
  | FullInversionClear
  deriving (Show)

data InversionStrength c d i
  = NonDepInversion InversionKind [i] (Maybe (OrVar (Located (OrAndIntroPatternExpr d))))
  | DepInversion InversionKind (Maybe c) (Maybe (OrVar (Located (OrAndIntroPatternExpr d))))
  | InversionUsing c [i]
  deriving (Show)

data Location a b
  = HypLocation a
  | ConclLocation b
  deriving (Show)

data MessageToken i
  = MsgString String
  | MsgInt Int
  | MsgIdent i
  deriving (Show)

type InductionClause d i =
  (
    InductionArg (WithBindings d),
    (
      Maybe (Located IntroPatternNamingExpr),
      Maybe (OrVar (Located (OrAndIntroPatternExpr d)))
    ),
    Maybe (ClauseExpr i)
  )

type InductionClauseList c d i =
  ([InductionClause d i], Maybe (WithBindings c))

type WithBindingsArg a = (ClearFlag, WithBindings a)

data Multi
  = Precisely Int
  | UpTo Int
  | RepeatStar
  | RepeatPlus
  deriving (Show)

data MatchPattern a
  = Term a
  | Subterm Bool (Maybe Id) a
  deriving (Show)

data MatchContextHyps a
  = Hyp (Located Name) (MatchPattern a)
  | Def (Located Name) (MatchPattern a) (MatchPattern a)
  deriving (Show)

data MatchRule a t
  = Pat [MatchContextHyps a] (MatchPattern a) t
  | All t
  deriving (Show)

data MLTacticName =
  MkMLTacticName
  { mlTacPlugin :: String
  , mlTacTactic :: String
  }
  deriving (Show)

data MLTacticEntry =
  MkMLTacticEntry
  { mlTacName :: MLTacticName
  , mlTacIndex :: Int
  }
  deriving (Show)

type GlobConstrAndExpr = (GlobConstr, Maybe ConstrExpr)
type OpenConstrExpr = ((), ConstrExpr)
type OpenGlobConstr = ((), GlobConstrAndExpr)
type GlobConstrPatternAndExpr = (GlobConstrAndExpr, ConstrPattern)
type DelayedOpenConstrWithBindings = Env -> EvarMap -> (EvarMap, WithBindings Constr)
type DelayedOpenConstr = Env -> EvarMap -> (EvarMap, Constr)
type IntroPattern = Located (IntroPatternExpr DelayedOpenConstr)
type IntroPatterns = [Located (IntroPatternExpr DelayedOpenConstr)]
type OrAndIntroPattern = Located (OrAndIntroPattern DelayedOpenConstr)
type IntroPatternNaming = Located IntroPatternNamingExpr

data GenAtomicTacticExpr a

{-
  (* Basic tactics *)
  = TacIntroPattern [Located of 'dtrm intro_pattern_expr located list
  | TacIntroMove of Id.t option * 'nam move_location
  | TacExact of 'trm
  | TacApply of advanced_flag * evars_flag * 'trm with_bindings_arg list *
      (clear_flag * 'nam * 'dtrm intro_pattern_expr located option) option
  | TacElim of evars_flag * 'trm with_bindings_arg * 'trm with_bindings option
  | TacCase of evars_flag * 'trm with_bindings_arg
  | TacFix of Id.t option * int
  | TacMutualFix of Id.t * int * (Id.t * int * 'trm) list
  | TacCofix of Id.t option
  | TacMutualCofix of Id.t * (Id.t * 'trm) list
  | TacAssert of
      bool * 'tacexpr option *
      'dtrm intro_pattern_expr located option * 'trm
  | TacGeneralize of ('trm with_occurrences * Name.t) list
  | TacGeneralizeDep of 'trm
  | TacLetTac of Name.t * 'trm * 'nam clause_expr * letin_flag *
      intro_pattern_naming_expr located option

  (* Derived basic tactics *)
  | TacInductionDestruct of
      rec_flag * evars_flag * ('trm,'dtrm,'nam) induction_clause_list
  | TacDoubleInduction of quantified_hypothesis * quantified_hypothesis

  (* Automation tactics *)
  | TacTrivial of debug * 'trm list * string list option
  | TacAuto of debug * int or_var option * 'trm list * string list option

  (* Context management *)
  | TacClear of bool * 'nam list
  | TacClearBody of 'nam list
  | TacMove of 'nam * 'nam move_location
  | TacRename of ('nam *'nam) list

  (* Trmuctors *)
  | TacSplit of evars_flag * 'trm bindings list

  (* Conversion *)
  | TacReduce of ('trm,'cst,'pat) red_expr_gen * 'nam clause_expr
  | TacChange of 'pat option * 'dtrm * 'nam clause_expr

  (* Equivalence relations *)
  | TacSymmetry of 'nam clause_expr

  (* Equality and inversion *)
  | TacRewrite of evars_flag *
      (bool * multi * 'dtrm with_bindings_arg) list * 'nam clause_expr *
      (* spiwack: using ['dtrm] here is a small hack, may not be
         stable by a change in the representation of delayed
         terms. Because, in fact, it is the whole "with_bindings"
         which is delayed. But because the "t" level for ['dtrm] is
         uninterpreted, it works fine here too, and avoid more
         disruption of this file. *)
      'tacexpr option
  | TacInversion of ('trm,'dtrm,'nam) inversion_strength * quantified_hypothesis

constraint 'a = <
    term:'trm;
    utrm: 'utrm;
    dterm: 'dtrm;
    pattern:'pat;
    constant:'cst;
    reference:'ref;
    name:'nam;
    tacexpr:'tacexpr;
    level:'lev
>

(** Possible arguments of a tactic definition *)

and 'a gen_tactic_arg =
  | TacDynamic     of Loc.t * Dyn.t
  | TacGeneric     of 'lev generic_argument
  | MetaIdArg      of Loc.t * bool * string
  | ConstrMayEval  of ('trm,'cst,'pat) may_eval
  | UConstr        of 'utrm
  | Reference      of 'ref
  | TacCall of Loc.t * 'ref *
      'a gen_tactic_arg list
  | TacFreshId of string or_var list
  | Tacexp of 'tacexpr
  | TacPretype of 'trm
  | TacNumgoals

constraint 'a = <
    term:'trm;
    utrm: 'utrm;
    dterm: 'dtrm;
    pattern:'pat;
    constant:'cst;
    reference:'ref;
    name:'nam;
    tacexpr:'tacexpr;
    level:'lev
>

(** Generic ltac expressions.
    't : terms, 'p : patterns, 'c : constants, 'i : inductive,
    'r : ltac refs, 'n : idents, 'l : levels *)

and 'a gen_tactic_expr =
  | TacAtom of Loc.t * 'a gen_atomic_tactic_expr
  | TacThen of
      'a gen_tactic_expr *
      'a gen_tactic_expr
  | TacDispatch of
      'a gen_tactic_expr list
  | TacExtendTac of
      'a gen_tactic_expr array *
      'a gen_tactic_expr *
      'a gen_tactic_expr array
  | TacThens of
      'a gen_tactic_expr *
      'a gen_tactic_expr list
  | TacThens3parts of
      'a gen_tactic_expr *
      'a gen_tactic_expr array *
      'a gen_tactic_expr *
      'a gen_tactic_expr array
  | TacFirst of 'a gen_tactic_expr list
  | TacComplete of 'a gen_tactic_expr
  | TacSolve of 'a gen_tactic_expr list
  | TacTry of 'a gen_tactic_expr
  | TacOr of
      'a gen_tactic_expr *
      'a gen_tactic_expr
  | TacOnce of
      'a gen_tactic_expr
  | TacExactlyOnce of
      'a gen_tactic_expr
  | TacIfThenCatch of
      'a gen_tactic_expr *
      'a gen_tactic_expr *
      'a gen_tactic_expr
  | TacOrelse of
      'a gen_tactic_expr *
      'a gen_tactic_expr
  | TacDo of int or_var * 'a gen_tactic_expr
  | TacTimeout of int or_var * 'a gen_tactic_expr
  | TacTime of string option * 'a gen_tactic_expr
  | TacRepeat of 'a gen_tactic_expr
  | TacProgress of 'a gen_tactic_expr
  | TacShowHyps of 'a gen_tactic_expr
  | TacAbstract of
      'a gen_tactic_expr * Id.t option
  | TacId of 'n message_token list
  | TacFail of global_flag * int or_var * 'n message_token list
  | TacInfo of 'a gen_tactic_expr
  | TacLetIn of rec_flag *
      (Id.t located * 'a gen_tactic_arg) list *
      'a gen_tactic_expr
  | TacMatch of lazy_flag *
      'a gen_tactic_expr *
      ('p,'a gen_tactic_expr) match_rule list
  | TacMatchGoal of lazy_flag * direction_flag *
      ('p,'a gen_tactic_expr) match_rule list
  | TacFun of 'a gen_tactic_fun_ast
  | TacArg of 'a gen_tactic_arg located
  (* For ML extensions *)
  | TacML of Loc.t * ml_tactic_entry * 'l generic_argument list
  (* For syntax extensions *)
  | TacAlias of Loc.t * KerName.t * (Id.t * 'l generic_argument) list

constraint 'a = <
    term:'t;
    utrm: 'utrm;
    dterm: 'dtrm;
    pattern:'p;
    constant:'c;
    reference:'r;
    name:'n;
    tacexpr:'tacexpr;
    level:'l
>

and 'a gen_tactic_fun_ast =
    Id.t option list * 'a gen_tactic_expr

constraint 'a = <
    term:'t;
    utrm: 'utrm;
    dterm: 'dtrm;
    pattern:'p;
    constant:'c;
    reference:'r;
    name:'n;
    tacexpr:'te;
    level:'l
>

(** Globalized tactics *)

type g_trm = glob_constr_and_expr
type g_utrm = g_trm
type g_pat = glob_constr_and_expr * constr_pattern
type g_cst = evaluable_global_reference and_short_name or_var
type g_ref = ltac_constant located or_var
type g_nam  = Id.t located

type g_dispatch =  <
    term:g_trm;
    utrm:g_utrm;
    dterm:g_trm;
    pattern:g_pat;
    constant:g_cst;
    reference:g_ref;
    name:g_nam;
    tacexpr:glob_tactic_expr;
    level:glevel
>

and glob_tactic_expr =
    g_dispatch gen_tactic_expr

type glob_atomic_tactic_expr =
    g_dispatch gen_atomic_tactic_expr

type glob_tactic_arg =
    g_dispatch gen_tactic_arg

(** Raw tactics *)

type r_trm = constr_expr
type r_utrm = r_trm
type r_pat = constr_pattern_expr
type r_cst = reference or_by_notation
type r_ref = reference
type r_nam  = Id.t located
type r_lev = rlevel

type r_dispatch =  <
    term:r_trm;
    utrm:r_utrm;
    dterm:r_trm;
    pattern:r_pat;
    constant:r_cst;
    reference:r_ref;
    name:r_nam;
    tacexpr:raw_tactic_expr;
    level:rlevel
>

and raw_tactic_expr =
    r_dispatch gen_tactic_expr

type raw_atomic_tactic_expr =
    r_dispatch gen_atomic_tactic_expr

type raw_tactic_arg =
    r_dispatch gen_tactic_arg

(** Interpreted tactics *)

type t_trm = Term.constr
type t_utrm = Glob_term.closed_glob_constr
type t_pat = constr_pattern
type t_cst = evaluable_global_reference
type t_ref = ltac_constant located
type t_nam  = Id.t

type t_dispatch =  <
    term:t_trm;
    utrm:t_utrm;
    dterm:g_trm;
    pattern:t_pat;
    constant:t_cst;
    reference:t_ref;
    name:t_nam;
    tacexpr:glob_tactic_expr;
    level:tlevel
>

type tactic_expr =
    t_dispatch gen_tactic_expr

type atomic_tactic_expr =
    t_dispatch gen_atomic_tactic_expr

type tactic_arg =
    t_dispatch gen_tactic_arg

(** Misc *)

type raw_red_expr = (r_trm, r_cst, r_pat) red_expr_gen
type glob_red_expr = (g_trm, g_cst, g_pat) red_expr_gen
-}
