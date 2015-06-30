module Coq.Intf.DeclKinds where

data Locality
  = Discharge
  | Local
  | Global
  deriving (Show)

data BindingKind
  = Explicit
  | Implicit
  deriving (Show)

type Polymorphic = Bool

type PrivateFlag = Bool

data TheoremKind
  = Theorem
  | Lemma
  | Fact
  | Remark
  | Property
  | Proposition
  | Corollary
  deriving (Show)

data DefinitionObjectKind
  = Definition
  | Coercion
  | SubClass
  | CanonicalStructure
  | Example
  | Fixpoint
  | CoFixpoint
  | Scheme
  | StructureComponent
  | IdentityCoercion
  | Instance
  | Method
  deriving (Show)

data AssumptionObjectKind
  = Definitional
  | Logical
  | Conjectural
  deriving (Show)

type AssumptionKind = (Locality, Polymorphic, AssumptionObjectKind)

type DefinitionKind = (Locality, Polymorphic, DefinitionObjectKind)

data GoalObjectKind
  = DefinitionBody DefinitionObjectKind
  | Proof TheoremKind
  deriving (Show)

type GoalKind = (Locality, Polymorphic, GoalObjectKind)

data LogicalKind
  = IsAssumption AssumptionObjectKind
  | IsDefinition DefinitionObjectKind
  | IsProof TheoremKind
  deriving (Show)

data RecursivityKind
  = Finite
  | CoFinite
  | BiFinite
  deriving (Show)
