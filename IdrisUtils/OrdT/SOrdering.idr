module IdrisUtils.OrdT.SOrdering

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Definition] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| Prelude.Interfaces.Ordering sans EQ.
data SOrdering : Type where
  LT : SOrdering
  GT : SOrdering

---------------------------------------------------------------------------------------------------
-- [Implementations] ------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

implementation Uninhabited (SOrdering.LT = SOrdering.GT) where
  uninhabited Refl impossible

implementation DecEq SOrdering where
  decEq LT LT = Yes Refl
  decEq GT GT = Yes Refl
  decEq LT GT = No absurd
  decEq GT LT = No (absurd . sym)
