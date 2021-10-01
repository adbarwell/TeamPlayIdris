module IdrisUtils.OrdS

import public IdrisUtils.Setoid
import public IdrisUtils.OrdT

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Definition] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| A strict total ordering over a given carrier type that has an equivalence relation s.t.
||| for all elements, `x` and `y`, and all proofs, `p` and `q`, of `x < y`, `p = q`.
|||
||| This 'singularity' proof (in the sense that only a single value may be constructed for the type)
||| is useful for proofs of contradiction.
|||
record StrictTotalOrderingS (c : Type) (setoid : SetoidT c) where
  constructor MkSTOrderingS
  ordT   : StrictTotalOrderingT c setoid
  ||| `∀ x,y : c . ∀ p,q : LT x y . p = q`
  singLT : (x,y : c) -> (p,q : ltR ordT x y) -> p = q

---------------------------------------------------------------------------------------------------
-- [Projections] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

proj_LT : StrictTotalOrderingS c setoid -> (c -> c -> Type)
proj_LT ordS = ltR (ordT ordS)

proj_Asym : (ordS : StrictTotalOrderingS c setoid)
         -> ((x,y : c) -> proj_LT ordS x y -> Not (proj_LT ordS y x))
proj_Asym ordS = asymLT (ordT ordS)

proj_Trans : (ordS : StrictTotalOrderingS c setoid)
          -> ((x,y,z : c) -> proj_LT ordS x y -> proj_LT ordS y z -> proj_LT ordS x z)
proj_Trans ordS = transLT (ordT ordS)

proj_Tricho : (ordS : StrictTotalOrderingS c setoid)
           -> ((x,y : c) -> Trichotomy setoid (proj_LT ordS) x y)
proj_Tricho ordS = trichoLT (ordT ordS)

proj_decLT : (ordS : StrictTotalOrderingS c setoid) -> ((x,y : c) -> Dec (proj_LT ordS x y))
proj_decLT ordS = decLT (ordT ordS)

---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
