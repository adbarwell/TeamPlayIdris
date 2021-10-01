module IdrisUtils.Nat

import IdrisUtils.Ord
import IdrisUtils.Decidability
import IdrisUtils.Equality

-- import Data.Vect
-- import IdrisUtils.Data.Vect.NotElem
-- import IdrisUtils.Data.Vect.IsSet

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [(Strict) Total Ordering] ----------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- [Definition] -----------------------------------------------------------------------------------

data LTNat : Nat -> Nat -> Type where
  LTZero : LTNat Z (S k)
  LTSucc : LTNat n m -> LTNat (S n) (S m)

GTNat : Nat -> Nat -> Type
GTNat x y = LTNat y x

-- [Uninhabited] ----------------------------------------------------------------------------------

implementation Uninhabited (LTNat x Z) where
  uninhabited LTZero impossible
  uninhabited LTSucc impossible

-- [Asymmetry, Transitivity, and Trichotomy] ------------------------------------------------------

asymLTNat : (x,y : Nat) -> LTNat x y -> Not (LTNat y x)
asymLTNat Z (S k) LTZero _ impossible
asymLTNat (S n) (S k) (LTSucc p) (LTSucc q) = asymLTNat n k p q

irrLTNat : (x : Nat) -> Not (LTNat x x)
irrLTNat x p = asymLTNat x x p p

transLTNat : (x,y,z : Nat) -> LTNat x y -> LTNat y z -> LTNat x z
transLTNat Z (S y) (S z) LTZero (LTSucc q) = LTZero
transLTNat (S x) (S y) (S z) (LTSucc p) (LTSucc q) = LTSucc (transLTNat x y z p q)

||| < on naturals is a congruence
congLTNat : LTNat n m -> LTNat (S n) (S m)
congLTNat LTZero = LTSucc LTZero
congLTNat (LTSucc lt) = LTSucc (LTSucc lt)

trichoLTNat : (x,y : Nat) -> Trichotomy (PropEqSetoid Nat Decidable.Equality.decEq) LTNat x y
trichoLTNat Z Z = IsEq (\p => absurd p)
trichoLTNat Z (S m) = IsBinR_xRy LTZero absurd absurd
trichoLTNat (S n) Z = IsBinR_yRx LTZero absurd absurd
trichoLTNat (S n) (S m) with (trichoLTNat n m)
  trichoLTNat (S n) (S n) | IsEq p' = IsEq (\p => asymLTNat (S n) (S n) p p)
  trichoLTNat (S n) (S m) | IsBinR_xRy p q' r' =
    IsBinR_xRy (congLTNat p) (\(LTSucc q) => q' q) (r' . succInjective n m)
  trichoLTNat (S n) (S m) | IsBinR_yRx p q' r' =
    IsBinR_yRx (congLTNat p) (\(LTSucc q) => q' q) (r' . succInjective n m)

-- [Decision Procedure] ---------------------------------------------------------------------------

decLTNat : (x,y : Nat) -> Dec (LTNat x y)
decLTNat Z Z = No absurd
decLTNat Z (S y) = Yes LTZero
decLTNat (S x) Z = No absurd
decLTNat (S x) (S y) with (decLTNat x y)
  decLTNat (S x) (S y) | Yes lt = Yes (LTSucc lt)
  decLTNat (S x) (S y) | No gte = No (\(LTSucc lt) => gte lt)
  
-- [Total Ordering (General Setoid)] --------------------------------------------------------------

StrictTotalOrderingTNat : StrictTotalOrderingT Nat (PropEqSetoid Nat Decidable.Equality.decEq)
StrictTotalOrderingTNat = MkSTOrderingT LTNat asymLTNat transLTNat trichoLTNat decLTNat

-- [Singleton] ------------------------------------------------------------------------------------

singLTNat : (x,y : Nat) -> (p,q : LTNat x y) -> p = q
singLTNat Z (S y) LTZero LTZero = Refl
singLTNat (S x) (S y) (LTSucc p) (LTSucc q) = rewrite (singLTNat x y p q) in Refl

-- [Total Ordering with Singleton] ----------------------------------------------------------------

StrictTotalOrderingSNat : StrictTotalOrderingS Nat (PropEqSetoid Nat Decidable.Equality.decEq)
StrictTotalOrderingSNat = MkSTOrderingS StrictTotalOrderingTNat singLTNat

-- [Total Ordering] -------------------------------------------------------------------------------

StrictTotalOrderingNat : StrictTotalOrdering Nat
StrictTotalOrderingNat = MkSTOrdering Decidable.Equality.decEq StrictTotalOrderingSNat

---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data IsZero : Nat -> Type where
  ItIsZero : IsZero Z

implementation Uninhabited (IsZero (S k)) where
  uninhabited ItIsZero impossible

decIsZero : (k : Nat) -> Dec (IsZero k)
decIsZero Z     = Yes ItIsZero
decIsZero (S k) = No absurd

data IsOne : Nat -> Type where
  ItIsOne : IsOne (S Z)

implementation Uninhabited (IsOne Z) where
  uninhabited ItIsOne impossible
implementation Uninhabited (IsOne (S (S k))) where
  uninhabited ItIsOne impossible

decIsOne : (k : Nat) -> Dec (IsOne k)
decIsOne Z         = No absurd
decIsOne (S Z)     = Yes ItIsOne
decIsOne (S (S k)) = No absurd

-- [Set] ------------------------------------------------------------------------------------------

{-
IsSetNat : (xs : Vect n Nat) -> Type
IsSetNat = IsSet TotalOrderingNat
-}

-- [Decidability] ---------------------------------------------------------------------------------

lemma_LT_sound : (x, y : Nat) -> (LTNat x y) -> Not (LTE y x)
lemma_LT_sound Z (S y) LTZero p = absurd p
lemma_LT_sound (S x) (S y) (LTSucc lt) (LTESucc lte) = lemma_LT_sound x y lt lte

lemma_LTE_sound : (x,y : Nat) -> (LTE y x) -> Not (LTNat x y)
lemma_LTE_sound x Z LTEZero p = absurd p
lemma_LTE_sound (S x) (S y) (LTESucc lte) (LTSucc lt) = lemma_LTE_sound x y lte lt

PropNat : (x,y : Nat) -> Prop
PropNat x y = MkProp (LTNat x y) (LTE y x)
                     (decLTNat x y) (isLTE y x)
                     (lemma_LT_sound x y) (lemma_LTE_sound x y)

decPLTNat : (x,y : Nat) -> PDec (PropNat x y)
decPLTNat Z Z = No LTEZero
decPLTNat (S x) Z = No LTEZero
decPLTNat Z (S y) = Yes LTZero
decPLTNat (S x) (S y) with (decPLTNat x y)
  | Yes p = Yes (LTSucc p)
  | No  q = No (LTESucc q)

DecidableNat : (x,y : Nat) -> Decidable (PropNat x y)
DecidableNat x y = IsDecidable (decPLTNat x y)

implementation StrictTotalOrder Nat where
  theOrder = StrictTotalOrderingNat

implementation LTSound Nat where
  lt_sound LTZero (Ord.IsLT _) impossible
  lt_sound {x = S x} (LTSucc p) IsEq = asymLTNat x x p p
  lt_sound {x = S x} {y = S y} (LTSucc p) (IsLT (LTSucc q)) = asymLTNat x y p q

  gte_sound {x = x} IsEq q = asymLTNat x x q q
  gte_sound {x = x} {y = y} (IsLT p) q = asymLTNat x y q p
