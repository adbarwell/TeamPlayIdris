module IdrisUtils.Equality

import public IdrisUtils.Ord
import public IdrisUtils.Decidability

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Propositional Inequality] ---------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| Proof that two values of the same type are not (propositionally) equal.
|||
||| Takes advantage of the fact that the given type is totally ordered to avoid equality proofs;
||| specifically, x ≠ y iff (x > y) \/ (x < y).
data NotEq : {ord : StrictTotalOrdering c} -> (x : c) -> (y : c) -> Type where
  IsLT : (lt : proj_LT ord x y) -> NotEq {ord} x y
  IsGT : (gt : proj_LT ord y x) -> NotEq {ord} x y

decNotEq_xEQy : (nlt : Not (proj_LT ord x y))
             -> (ngt : Not (proj_LT ord y x))
             -> Not (NotEq {ord} x y)
decNotEq_xEQy nlt ngt (IsLT lt) = nlt lt
decNotEq_xEQy nlt ngt (IsGT gt) = ngt gt

decNotEq : (ord : StrictTotalOrdering c) -> (x,y : c) -> Dec (NotEq {ord = ord} x y)
decNotEq ord x y with (proj_decLT ord x y)
  | Yes lt = Yes (IsLT lt)
  | No nlt with (proj_decLT ord y x)
    | Yes gt = Yes (IsGT gt)
    | No ngt = No (decNotEq_xEQy nlt ngt)

---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

lemma_NotEq_sound : (p : NotEq x y) -> Not (x = y)
lemma_NotEq_sound {x} (IsLT {ord} lt) Refl = proj_Asym ord x x lt lt
lemma_NotEq_sound {x} (IsGT {ord} gt) Refl = proj_Asym ord x x gt gt

lemma_NotEq_singleton : (ord : StrictTotalOrdering c) -> (x : c) -> (y : c)
                     -> (p : NotEq {ord = ord} x y) -> (q : NotEq {ord = ord} x y) -> p = q
lemma_NotEq_singleton ord x y (IsLT p) (IsLT q) with (singLT (ordS ord) x y p q)
  lemma_NotEq_singleton ord x y (IsLT p) (IsLT p) | Refl = Refl
lemma_NotEq_singleton ord x y (IsLT p) (IsGT q) with (proj_Asym ord x y p q)
  lemma_NotEq_singleton ord x y (IsLT p) (IsGT q) | _ impossible
lemma_NotEq_singleton ord x y (IsGT p) (IsGT q) with (singLT (ordS ord) y x p q)
  lemma_NotEq_singleton ord x y (IsGT p) (IsGT p) | Refl = Refl
lemma_NotEq_singleton ord x y (IsGT p) (IsLT q) with (proj_Asym ord y x p q)
  lemma_NotEq_singleton ord x y (IsGT p) (IsLT q) | _ impossible

lemma_NotEq_irreflexive : (p : NotEq x x) -> Void
lemma_NotEq_irreflexive {x} (IsLT {ord} lt) = proj_Asym ord x x lt lt
lemma_NotEq_irreflexive {x} (IsGT {ord} gt) = proj_Asym ord x x gt gt

---------------------------------------------------------------------------------------------------
-- [Decidability] ---------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

record HasDecEq (c : Type) where
  constructor ItHasDecEq
  theFun : (x,y : c) -> Dec (x = y)

lemma_PropEq_sound : (x = y) -> Not (NotEq x y)
lemma_PropEq_sound {x} Refl (IsLT {ord} p) = proj_Asym ord x x p p
lemma_PropEq_sound {x} Refl (IsGT {ord} p) = proj_Asym ord x x p p

PropDecEqT : (ord : StrictTotalOrdering c) -> (x, y : c) -> Prop
PropDecEqT ord x y =
  MkProp (x = y) (NotEq {ord = ord} x y)
         (decEq ord x y) (decNotEq ord x y)
         lemma_PropEq_sound lemma_NotEq_sound

-- interface StrictTotalOrder c => PropDecEq c where

decPEq : LTSound c => (x, y : c) -> PDec (PropDecEqT (Ord.theOrder {c = c}) x y)
decPEq x y with (proj_Tricho Ord.theOrder x y)
  decPEq x y | IsBinR_xRy p nq nr = No (IsLT p)
  decPEq x x | IsEq np = Yes Refl
  decPEq x y | IsBinR_yRx q np nr = No (IsGT q)

{-
PDecEq : (dec : HasDecEq c) -> (ord : StrictTotalOrdering c)
      -> (x,y : c) -> Decidable (PropDecEqT dec ord x y)
PDecEq dec ord x y = IsDecidable (decEq x y)
-}




