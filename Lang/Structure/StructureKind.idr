module StructureKind

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data StructKind : Type where
  -- Setoid : StructKind
  Magma : StructKind
  Semigroup : StructKind
  Monoid : StructKind
  Group : StructKind
  AbGroup : StructKind
  Ring : StructKind

---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data HasPlus : (kind : StructKind) -> Type where
  MagmaHasPlus : HasPlus Magma
  SemigroupHasPlus : HasPlus Semigroup
  MonoidHasPlus : HasPlus Monoid
  GroupHasPlus : HasPlus Group
  AbGroupHasPlus : HasPlus AbGroup
  RingHasPlus : HasPlus Ring

data HasSub : (kind : StructKind) -> Type where
  GroupHasSub : HasSub Group
  AbGroupHasSub : HasSub AbGroup
  RingHasSub : HasSub Ring

data HasMul : (kind : StructKind) -> Type where
  RingHasMul : HasMul Ring

