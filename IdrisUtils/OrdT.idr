module IdrisUtils.OrdT

import public IdrisUtils.Setoid
import public IdrisUtils.Trichotomy

import public IdrisUtils.OrdT.SOrdering

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Definition] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| A strict total ordering for a given carrier type that has an equivalence relation.
record StrictTotalOrderingT (c : Type) (setoid : SetoidT c) where
  constructor MkSTOrderingT
  ||| The relation (strictly less-than).
  ltR      : c -> c -> Type
  ||| A proof that the relation is asymmetric; implies irreflexivity.
  asymLT   : (x,y : c) -> ltR x y -> Not (ltR y x)
  ||| A proof that the relation is transitive.
  transLT  : (x,y,z : c) -> ltR x y -> ltR y z -> ltR x z
  ||| A proof that the relation is trichotomous.
  trichoLT : (x,y : c) -> Trichotomy setoid ltR x y

  decLT : (x,y : c) -> Dec (ltR x y)

---------------------------------------------------------------------------------------------------
-- [Interface] ------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

interface Setoid c => StrictTotalOrderT c where
  order : StrictTotalOrderingT c (Setoid.setoid {c = c})

---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------


