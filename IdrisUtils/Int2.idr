module IdrisUtils.Integer

import public IdrisUtils.OrdT
import public IdrisUtils.Nat

-- import public Lang.Structure

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Definition] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| Signed integers.
|||
||| Represented as a pair of naturals, `(a,b)`, s.t. the pair stands for the result of subtracting 
||| `b` from `a`. If a ≥ b then a - b else -(b - a).
data SInt : Type where
  MkSInt : (a : Nat) -> (b : Nat) -> SInt

fromIntegerSInt : Integer -> SInt
fromIntegerSInt n =
  if n < 0 then MkSInt Z (fromIntegerNat (abs n)) else MkSInt (fromIntegerNat (abs n)) Z

---------------------------------------------------------------------------------------------------
-- [Equivalence] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- [Definition] -----------------------------------------------------------------------------------

data EqSInt : (x,y : SInt) -> Type where
  MkEq : (prf : a + d = b + c) -> EqSInt (MkSInt a b) (MkSInt c d)

-- [Symmetry and Transitivity] --------------------------------------------------------------------

symEqSInt : (x,y : SInt) -> (p : EqSInt x y) -> EqSInt y x
symEqSInt (MkSInt a b) (MkSInt c d) (MkEq prf) =
  MkEq (rewrite plusCommutative d a in rewrite plusCommutative c b in (sym prf))

trnsEqSInt' : (a,b,c,d,e,f : Nat)
           -> (p : EqSInt (MkSInt a b) (MkSInt c d))
           -> (q : EqSInt (MkSInt c d) (MkSInt e f))
           -> EqSInt (MkSInt a b) (MkSInt e f)
trnsEqSInt' Z Z c c e f (MkEq Refl) (MkEq q) =
  MkEq (rewrite plusLeftCancel c f e q in Refl)
trnsEqSInt' Z (S b) c Z e f (MkEq Refl) (MkEq q) impossible
trnsEqSInt' Z (S b) c (S (plus b c)) e f (MkEq Refl) (MkEq q) =
  let r = replace {P=(\x => plus c f = S (plus x e))} (plusCommutative b c) q
      s = replace {P=(\x => plus c f = S x)} (sym (plusAssociative c b e)) r
      t = replace {P=(\x => plus c f = x)} (plusSuccRightSucc c (b + e)) s
  in MkEq (plusLeftCancel c f (S (plus b e)) t)
trnsEqSInt' (S a) Z Z d e f (MkEq Refl) (MkEq q) impossible
trnsEqSInt' (S a) Z (S (plus a d)) d e f (MkEq Refl) (MkEq q) =
  let r = replace {P=(\x => S (plus x f) = plus d e)} (plusCommutative a d) q
      s = replace {P=(\x => S x = plus d e)} (sym (plusAssociative d a f)) r
      t = replace {P=(\x => x = plus d e)} (plusSuccRightSucc d (a + f)) s
  in MkEq (plusLeftCancel d (S (plus a f)) e t)
trnsEqSInt' (S a) (S b) c d e f (MkEq p) (MkEq q) =
  case trnsEqSInt' a b c d e f (MkEq (succInjective (plus a d) (plus b c) p)) (MkEq q) of
    MkEq r => MkEq (cong r)

trnsEqSInt : (x,y,z : SInt) -> (p : EqSInt x y) -> (q : EqSInt y z) -> EqSInt x z
trnsEqSInt (MkSInt a b) (MkSInt c d) (MkSInt e f) p q = trnsEqSInt' a b c d e f p q

-- [Setoid] ---------------------------------------------------------------------------------------

SetoidSInt : SetoidT SInt
SetoidSInt = MkSetoid EqSInt symEqSInt trnsEqSInt

-- [DecEq] ----------------------------------------------------------------------------------------

decEqSInt : (x,y : SInt) -> Dec (EqSInt x y)
decEqSInt (MkSInt a b) (MkSInt c d) with (decEq (a + d) (b + c))
  decEqSInt (MkSInt a b) (MkSInt c d) | Yes prf = Yes (MkEq prf)
  decEqSInt (MkSInt a b) (MkSInt c d) | No  neq = No (\(MkEq eq) => neq eq)

---------------------------------------------------------------------------------------------------
-- [Total Ordering] -------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- [Definition] -----------------------------------------------------------------------------------

data LTSInt : (x,y : SInt) -> Type where
  MkLTSInt : (lt : LTNat (a + d) (b + c)) -> LTSInt (MkSInt a b) (MkSInt c d)

-- [Asymmetry, Transitivity, and Trichotomy] ------------------------------------------------------

{-
irreflLTSInt : (x : SInt) -> (p : LTSInt x x) -> Void
irreflLTSInt (MkSInt a b) (MkLTSInt p) =
  let q = replace {P=LTNat (a + b)} (plusCommutative b a) p in asymLTNat (a + b) (a + b) q q
-}

asymLTSInt : (x, y : SInt) -> (p : LTSInt x y) -> (q : LTSInt y x) -> Void
asymLTSInt (MkSInt a b) (MkSInt c d) (MkLTSInt p) (MkLTSInt q) =
  asymLTNat (d + a) (c + b) (replace {P=uncurry LTNat} bothCommutative p) q where
    bothCommutative : (a + d, b + c) = (d + a, c + b)
    bothCommutative = rewrite plusCommutative a d in rewrite plusCommutative b c in Refl

transLTSInt' : (a,b,c,d,e,f : Nat)
            -> (p : LTSInt (MkSInt a b) (MkSInt c d))
            -> (q : LTSInt (MkSInt c d) (MkSInt e f))
            -> LTSInt (MkSInt a b) (MkSInt e f)
transLTSInt' Z Z c d e f (MkLTSInt p) (MkLTSInt q) = MkLTSInt ?holeHere
transLTSInt' Z (S b) c d e f (MkLTSInt p) (MkLTSInt q) = MkLTSInt ?holeHere
transLTSInt' (S a) Z c d e f (MkLTSInt p) (MkLTSInt q) = MkLTSInt ?holeHere
transLTSInt' (S a) (S b) c d e f (MkLTSInt p) (MkLTSInt q) = MkLTSInt ?holeHere

transLTSInt : (x, y, z : SInt) -> (p : LTSInt x y) -> (q : LTSInt y z) -> LTSInt x z
transLTSInt (MkSInt a b) (MkSInt c d) (MkSInt e f) p q = transLTSInt' a b c d e f p q

-- [Singleton] ------------------------------------------------------------------------------------

singSInt : (x,y : SInt) -> (p,q : LTSInt x y) -> p = q
singSInt (MkSInt a b) (MkSInt c d) (MkLTSInt p) (MkLTSInt q) with (singLTNat (a + d) (b + c) p q)
  singSInt (MkSInt a b) (MkSInt c d) (MkLTSInt p) (MkLTSInt p) | Refl = Refl

-- [Decision Procedure] ---------------------------------------------------------------------------

isLTSInt : (x,y : SInt) -> Dec (LTSInt x y)
isLTSInt (MkSInt a b) (MkSInt c d) with (decLTNat (a + d) (b + c))
  | No gte = No (\(MkLTSInt lt) => gte lt)
  | Yes lt = Yes (MkLTSInt lt)
