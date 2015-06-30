module Coq.Intf.GlobTerm where

import Coq.Intf.DeclKinds
import Coq.Intf.MiscTypes
import Coq.Kernel.Names
import Coq.Library.GlobNames

type ExistentialName = Id

data CasesPattern
  = PatVar Loc Name
  | PatCstr Loc Constructor [CasesPattern] Name
  deriving (Show)

data GlobConstr
  = GRef Loc GlobalReference (Maybe [GlobLevel])
  | GVar Loc Id
  | GEvar Loc ExistentialName [(Id, GlobConstr)]
  | GPatVar Loc (Bool, PatVar)
  | GApp Loc GlobConstr [GlobConstr]
  | GLambda Loc Name BindingKind GlobConstr GlobConstr
  | GProd Loc Name BindingKind GlobConstr GlobConstr
  | GLetIn Loc Name GlobConstr GlobConstr
  | GCases Loc CaseStyle (Maybe GlobConstr) ToMatchTuples CasesClauses
      (** [GCases(l,style,r,tur,cc)] = "match 'tur' return 'r' with 'cc'" (in
	  [MatchStyle]) *)
  | GLetTuple of Loc.t * Name.t list * (Name.t * glob_constr option) *
      glob_constr * glob_constr
  | GIf of Loc.t * glob_constr * (Name.t * glob_constr option) * glob_constr * glob_constr
  | GRec of Loc.t * fix_kind * Id.t array * glob_decl list array *
      glob_constr array * glob_constr array
  | GSort of Loc.t * glob_sort
  | GHole of (Loc.t * Evar_kinds.t * intro_pattern_naming_expr * Genarg.glob_generic_argument option)
  | GCast of Loc.t * glob_constr * glob_constr cast_type
