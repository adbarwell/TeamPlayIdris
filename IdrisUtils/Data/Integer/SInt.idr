module IdrisUtils.Data.Integer.SInt

import public IdrisUtils.Ord
import public IdrisUtils.Nat
import public IdrisUtils.Data.Sign
import public IdrisUtils.Decidability
import public IdrisUtils.Equality

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Definition] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| Agda Style
data SInt : Type where
  Pos : Nat -> SInt
  Neg : Nat-> SInt

---------------------------------------------------------------------------------------------------
-- [DecEq] ----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

implementation Uninhabited (Pos x = Neg y) where
  uninhabited Refl impossible

decEqSInt : (x,y : SInt) -> Dec (x = y)
decEqSInt (Pos x) (Pos y) with (decEq x y)
  decEqSInt (Pos x) (Pos x) | Yes Refl = Yes Refl
  decEqSInt (Pos x) (Pos y) | No neq = No (\Refl => neq Refl)
decEqSInt (Pos x) (Neg y) = No absurd
decEqSInt (Neg x) (Pos y) = No (absurd . sym)
decEqSInt (Neg x) (Neg y) with (decEq x y)
  decEqSInt (Neg x) (Neg x) | Yes Refl = Yes Refl
  decEqSInt (Neg x) (Neg y) | No neq = No (\Refl => neq Refl)

---------------------------------------------------------------------------------------------------
-- [(Strict) Total Ordering] ----------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- [Definition] -----------------------------------------------------------------------------------

data LTSInt : (x,y : SInt) -> Type where
  PosLTPos : (lt : LTNat x y) -> LTSInt (Pos x) (Pos y)
  NegLTNeg : (lt : LTNat y x) -> LTSInt (Neg x) (Neg y)
  NegLTPos : LTSInt (Neg x) (Pos y)

-- [Uninhabited] ----------------------------------------------------------------------------------

implementation Uninhabited (LTSInt (Pos x) (Neg y)) where
  uninhabited PosLTPos impossible
  uninhabited NegLTNeg impossible
  uninhabited NegLTPos impossible

-- [Asymmetry, Transitivity, and Trichotomy] ------------------------------------------------------

asymLTSInt : (x,y : SInt) -> LTSInt x y -> Not (LTSInt y x)
asymLTSInt (Pos x) (Pos y) (PosLTPos p) (PosLTPos q) = asymLTNat x y p q
asymLTSInt (Neg x) (Neg y) (NegLTNeg p) (NegLTNeg q) = asymLTNat x y q p

transLTSInt : (x,y,z : SInt) -> LTSInt x y -> LTSInt y z -> LTSInt x z
transLTSInt (Pos x) (Pos y) (Pos z) (PosLTPos p) (PosLTPos q) =
  PosLTPos (transLTNat x y z p q)
transLTSInt (Neg x) (Pos y) (Pos z) NegLTPos (PosLTPos q) = NegLTPos
transLTSInt (Neg x) (Neg y) (Neg z) (NegLTNeg p) (NegLTNeg q) =
  NegLTNeg (transLTNat z y x q p)
transLTSInt (Neg x) (Neg y) (Pos z) (NegLTNeg p) NegLTPos = NegLTPos

posInjective : (left, right : Nat) -> (p : Pos left = Pos right) -> left = right
posInjective left left Refl = Refl

negInjective : (left, right : Nat)
            -> (p : Neg left = Neg right)
            -> left = right
negInjective left left Refl = Refl

trichoLTSInt : (x,y : SInt) -> Trichotomy (PropEqSetoid SInt SInt.decEqSInt) LTSInt x y
trichoLTSInt (Pos x) (Pos y) with (trichoLTNat x y)
  trichoLTSInt (Pos x) (Pos x) | (IsEq p') = (IsEq (\(PosLTPos p) => p' p))
  trichoLTSInt (Pos x) (Pos y) | (IsBinR_xRy p q' r') =
    IsBinR_xRy (PosLTPos p) (\(PosLTPos q) => q' q) (r' . posInjective x y)
  trichoLTSInt (Pos x) (Pos y) | (IsBinR_yRx p q' r') =
    IsBinR_yRx (PosLTPos p) (\(PosLTPos q) => q' q) (r' . posInjective x y)
trichoLTSInt (Pos x) (Neg y) = IsBinR_yRx NegLTPos absurd absurd
trichoLTSInt (Neg x) (Pos y) = IsBinR_xRy NegLTPos (\p => absurd p) (absurd . sym)
trichoLTSInt (Neg x) (Neg y) with (trichoLTNat x y)
  trichoLTSInt (Neg x) (Neg x) | (IsEq p') =
    IsEq (\(NegLTNeg p) => p' p)
  trichoLTSInt (Neg x) (Neg y) | (IsBinR_xRy p q' r') =
    IsBinR_yRx (NegLTNeg p) (\(NegLTNeg q) => q' q) (r' . negInjective x y)
  trichoLTSInt (Neg x) (Neg y) | (IsBinR_yRx p q' r') =
    IsBinR_xRy (NegLTNeg p) (\(NegLTNeg q) => q' q) (r' . negInjective x y)

-- [Decision Procedure] ---------------------------------------------------------------------------

decLTSInt : (x,y : SInt) -> Dec (LTSInt x y)
decLTSInt (Pos x) (Pos y) with (decLTNat x y)
  decLTSInt (Pos x) (Pos y) | Yes lt = Yes (PosLTPos lt)
  decLTSInt (Pos x) (Pos y) | No gte = No (\(PosLTPos lt) => gte lt)
decLTSInt (Pos x) (Neg y) = No absurd
decLTSInt (Neg x) (Pos y) = Yes NegLTPos
decLTSInt (Neg x) (Neg y) with (decLTNat y x)
  decLTSInt (Neg x) (Neg y) | Yes lt = Yes (NegLTNeg lt)
  decLTSInt (Neg x) (Neg y) | No gte = No (\(NegLTNeg lt) => gte lt)

-- [Total Ordering (General Setoid)] --------------------------------------------------------------

StrictTotalOrderingTSInt : StrictTotalOrderingT SInt (PropEqSetoid SInt SInt.decEqSInt)
StrictTotalOrderingTSInt = MkSTOrderingT LTSInt asymLTSInt transLTSInt trichoLTSInt decLTSInt

-- [Singleton] ------------------------------------------------------------------------------------

singLTSInt : (x,y : SInt) -> (p,q : LTSInt x y) -> p = q
singLTSInt (Pos x) (Pos y) (PosLTPos p) (PosLTPos q) = rewrite (singLTNat x y p q) in Refl
singLTSInt (Neg x) (Pos y) NegLTPos NegLTPos = Refl
singLTSInt (Neg x) (Neg y) (NegLTNeg p) (NegLTNeg q) = rewrite (singLTNat y x p q) in Refl

-- [Total Ordering with Singleton] ----------------------------------------------------------------

StrictTotalOrderingSSInt : StrictTotalOrderingS SInt (PropEqSetoid SInt SInt.decEqSInt)
StrictTotalOrderingSSInt = MkSTOrderingS StrictTotalOrderingTSInt singLTSInt

-- [Total Ordering] -------------------------------------------------------------------------------

StrictTotalOrderingSInt : StrictTotalOrdering SInt
StrictTotalOrderingSInt = MkSTOrdering decEqSInt StrictTotalOrderingSSInt

implementation StrictTotalOrder SInt where
  theOrder = StrictTotalOrderingSInt

---------------------------------------------------------------------------------------------------
-- [Positive Decidability] ------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

implementation LTSound SInt where
  lt_sound {x = Pos x} (PosLTPos p) IsEq = asymLTNat x x p p
  lt_sound {x = Pos x} {y = Pos y} (PosLTPos p) (IsLT (PosLTPos q)) = asymLTNat x y p q
  lt_sound NegLTPos (Ord.IsLT _) impossible
  lt_sound {x = Neg x} (NegLTNeg p) IsEq = asymLTNat x x p p
  lt_sound {x = Neg x} {y = Neg y} (NegLTNeg p) (IsLT (NegLTNeg q)) = asymLTNat y x p q

  gte_sound {x = x} IsEq q = asymLTSInt x x q q
  gte_sound {x = x} {y = y} (IsLT p) q = asymLTSInt y x p q

---------------------------------------------------------------------------------------------------
-- [Conversions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

absSInt : SInt -> SInt
absSInt (Pos n) = Pos n
absSInt (Neg n) = (Pos (S n))

absSIntNat : SInt -> Nat
absSIntNat (Pos n) = n
absSIntNat (Neg n) = (S n)

||| Convert an Integer to a SInt.
fromIntegerSInt : Integer -> SInt
fromIntegerSInt 0 = Pos Z
fromIntegerSInt n =
  if (n > 0)
    then
      Pos (S (fromIntegerNat (assert_smaller n (n - 1))))
    else
      Neg (fromIntegerNat (assert_smaller n (abs n - 1)))

||| Convert a SInt to an Integer.
toIntegerSInt : SInt -> Integer
toIntegerSInt (Pos n) = toIntegerNat n
toIntegerSInt (Neg n) = -(toIntegerNat (S n))

---------------------------------------------------------------------------------------------------
-- [Sign] -----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

sign : SInt -> Sign
sign (Pos n) = Positive
sign (Neg n) = Negative

ctrSInt : Sign -> Nat -> SInt
ctrSInt _ Z = Pos Z
ctrSInt Positive (S n) = Pos (S n)
ctrSInt Negative (S n) = Neg n

ctrSIntLeftInverse : (i : SInt) -> ctrSInt (sign i) (absSIntNat i) = i
ctrSIntLeftInverse (Neg n) = Refl
ctrSIntLeftInverse (Pos Z) = Refl
ctrSIntLeftInverse (Pos (S n)) = Refl

data SignAbs : SInt -> Type where
  MkSignAbs : (s : Sign) -> (n : Nat) -> SignAbs (ctrSInt s n)

signAbs : (i : SInt) -> SignAbs i
signAbs i = rewrite sym (ctrSIntLeftInverse i) in MkSignAbs (sign i) (absSIntNat i)

---------------------------------------------------------------------------------------------------
-- [Basic Arithmetic Operations] ------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| Negates an integer.
negate : SInt -> SInt
negate (Pos Z) = Pos Z
negate (Pos (S n)) = Neg n
negate (Neg n) = Pos (S n)

subNat : (x,y : Nat) -> SInt
subNat m Z = Pos m
subNat Z (S m) = Neg m
subNat (S n) (S m) = subNat n m

||| Add two integers.
plus : SInt -> SInt -> SInt
plus (Neg x) (Neg y) = Neg (S (x + y))
plus (Neg x) (Pos y) = subNat y (S x)
plus (Pos x) (Neg y) = subNat x (S y)
plus (Pos x) (Pos y) = Pos (x + y) 

||| Subtract integers. Uses `negate`.
minus : SInt -> SInt -> SInt
minus x y = plus x (negate y)

succ : SInt -> SInt
succ i = plus (Pos (S Z)) i

pred : SInt -> SInt
pred i = plus (negate (Pos (S Z))) i

||| Multiply integers.
mult : SInt -> SInt -> SInt
mult i j = ctrSInt (sign i * sign j) (absSIntNat i * absSIntNat j)

---------------------------------------------------------------------------------------------------
-- [Interface implementations] --------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

implementation Eq SInt where
  (Pos n) == (Pos m) = n == m
  (Neg n) == (Neg m) = n == m
  _ == _ = False

implementation Cast SInt Integer where
  cast = toIntegerSInt

implementation Cast Integer SInt where
  cast = fromIntegerSInt

implementation Cast String SInt where
  cast orig = fromIntegerSInt (cast orig)

implementation Ord SInt where
  compare (Pos Z) (Pos Z) = EQ
  compare (Pos Z) (Pos (S m)) = LT
  compare (Pos (S n)) (Pos Z) = GT
  compare (Pos (S n)) (Pos (S m)) = compare n m
  compare (Pos n) (Neg m) = GT
  compare (Neg n) (Pos m) = LT
  compare (Neg n) (Neg m) = compare m n

implementation Num SInt where
  (+) = plus
  (*) = mult

  fromInteger = fromIntegerSInt

implementation Abs SInt where
  abs = absSInt

implementation Neg SInt where
  negate = SInt.negate
  (-) = minus

implementation Show SInt where
  show (Pos n) = show n
  show (Neg n) = "-" ++ show (S n)

---------------------------------------------------------------------------------------------------
-- [Properties of subNat] -------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

subNatSameArgsEqZero : (n : Nat) -> subNat n n = Pos Z
subNatSameArgsEqZero Z = Refl
subNatSameArgsEqZero (S n) = subNatSameArgsEqZero n

---------------------------------------------------------------------------------------------------
-- [Properties of plus] ---------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

plusCommutative : (x,y : SInt) -> x + y = y + x
plusCommutative (Neg x) (Neg y) =
  cong {f = (\n => Neg (S n))} (plusCommutative x y)
plusCommutative (Pos x) (Pos y) = cong {f = Pos} (plusCommutative x y)
plusCommutative (Neg x) (Pos y) = Refl
plusCommutative (Pos x) (Neg y) = Refl

plusLeftIdentity : (right : SInt) -> Pos Z + right = right
plusLeftIdentity (Pos n) = Refl
plusLeftIdentity (Neg n) = Refl

plusRightIdentity : (left : SInt) -> left + (Pos Z) = left
plusRightIdentity (Pos n) = plusRightIdentityPos n where
  plusRightIdentityPos : (left : Nat) -> (Pos left) + (Pos Z) = (Pos left)
  plusRightIdentityPos n = rewrite plusZeroRightNeutral n in Refl
plusRightIdentity (Neg n) = Refl

subNatLeftDistribOverPos : (x,y,z : Nat) -> (subNat y z) + (Pos x) = subNat (y + x) z
subNatLeftDistribOverPos _ Z Z = Refl
subNatLeftDistribOverPos _ Z (S _) = Refl
subNatLeftDistribOverPos _ (S _) Z = Refl
subNatLeftDistribOverPos x (S y) (S z) = subNatLeftDistribOverPos x y z

subNatLeftDistribOverNeg : (x,y,z : Nat) -> subNat y z + (Neg x) = subNat y (S z + x)
subNatLeftDistribOverNeg _ Z Z = Refl
subNatLeftDistribOverNeg _ Z (S z) = Refl
subNatLeftDistribOverNeg _ (S y) Z = Refl
subNatLeftDistribOverNeg x (S y) (S z) = subNatLeftDistribOverNeg x y z

subNatRightDistribOverPos : (x,y,z : Nat) -> (Pos x) + (subNat y z) = subNat (x + y) z
subNatRightDistribOverPos x y z =
  rewrite plusCommutative (Pos x) (subNat y z) in
    rewrite subNatLeftDistribOverPos x y z in
      cong {f = (\w => subNat w z)} (plusCommutative y x)

subNatRightDistribOverNeg : (x,y,z : Nat) -> (Neg x) + (subNat y z) = subNat y (S x + z)
subNatRightDistribOverNeg x y z =
  rewrite plusCommutative (Neg x) (subNat y z) in
    rewrite subNatLeftDistribOverNeg x y z in
      cong {f = (\w => subNat y (S w))} (plusCommutative z x)

plusAssociative : (x,y,z : SInt) -> (x + y) + z = x + (y + z)
plusAssociative (Pos Z) y z =
  rewrite plusLeftIdentity (y + z) in rewrite plusLeftIdentity y in Refl
plusAssociative x (Pos Z) z =
  rewrite plusLeftIdentity z in rewrite plusRightIdentity x in Refl
plusAssociative x y (Pos Z) =
  rewrite plusRightIdentity y in rewrite plusRightIdentity (x + y) in Refl
plusAssociative (Neg x) (Neg y) (Pos (S z)) = sym (subNatRightDistribOverNeg x z y)
plusAssociative (Neg x) (Pos (S y)) (Pos (S z)) = subNatLeftDistribOverPos (S z) y x
plusAssociative (Pos (S x)) (Neg y) (Neg z) = subNatLeftDistribOverNeg z x y
plusAssociative (Pos (S x)) (Neg y) (Pos (S z)) =
  rewrite subNatLeftDistribOverPos (S z) x y in
    rewrite subNatRightDistribOverPos (S x) z y in
      rewrite plusAssociative x (S Z) z in
        rewrite plusCommutative x (S Z) in
          Refl
plusAssociative (Pos (S x)) (Pos (S y)) (Neg z) =
  rewrite subNatRightDistribOverPos (S x) y z in
    rewrite plusAssociative x (S Z) y in
      rewrite plusCommutative x (S Z) in
        Refl
plusAssociative (Neg x) (Neg y) (Neg z) =
  rewrite plusAssociative x (S Z) (y + z) in
    rewrite plusCommutative x (S Z) in
      rewrite sym (plusAssociative x y z) in
        Refl
plusAssociative (Neg x) (Pos (S y)) (Neg z) = 
  rewrite subNatRightDistribOverNeg x y z in
    rewrite subNatLeftDistribOverNeg z y x in
      Refl
plusAssociative (Pos (S x)) (Pos (S y)) (Pos (S z)) =
  rewrite sym (plusAssociative (S x) (S y) (S z)) in Refl

plusLeftInverse : (x : SInt) -> x + (negate x) = (Pos Z)
plusLeftInverse (Neg n) = subNatSameArgsEqZero n
plusLeftInverse (Pos Z) = Refl
plusLeftInverse (Pos (S n)) = subNatSameArgsEqZero n

plusRightInverse : (x : SInt) -> (negate x) + x = (Pos Z)
plusRightInverse x = rewrite plusCommutative (negate x) x in plusLeftInverse x

---------------------------------------------------------------------------------------------------
-- [Properties of mult] ---------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

multCommutative : (x,y : SInt) -> x * y = y * x
multCommutative (Neg x) (Neg y) = rewrite multCommutative (S x) (S y) in Refl
multCommutative (Neg x) (Pos y) = rewrite multCommutative (S x) y in Refl
multCommutative (Pos x) (Neg y) = rewrite multCommutative x (S y) in Refl
multCommutative (Pos x) (Pos y) = rewrite multCommutative x y in Refl

multLeftIdentity : (x : SInt) -> (Pos (S Z)) * x = x
multLeftIdentity (Neg n) = rewrite plusZeroRightNeutral n in Refl
multLeftIdentity (Pos Z) = Refl
multLeftIdentity (Pos (S n)) = rewrite plusZeroRightNeutral n in Refl

multRightIdentity : (x : SInt) -> x * (Pos (S Z)) = x
multRightIdentity x = rewrite multCommutative x (Pos (S Z)) in multLeftIdentity x

multLeftZero : (x : SInt) -> (Pos Z) * x = (Pos Z)
multLeftZero n = Refl

multRightZero : (x : SInt) -> x * (Pos Z) = (Pos Z)
multRightZero n = rewrite multCommutative n (Pos Z) in multLeftZero n

||| Not (yet) implemented because Agda uses a ring solver (+-*-solver) which Idris doesn't have.
||| Frank's work might help here, but I don't know how well that would actually work...
||| Otherwise, will need to do this by hand (later).
|||
||| Note that this currently uses a `believe_me`.
multAssociative : (x,y,z : SInt) -> (x * y) * z = x * (y * z)
multAssociative x y z = believe_me ()
{-
multAssociative (Pos Z) _ _ = Refl
multAssociative x (Pos Z) z = rewrite multZeroRightZero (absSIntNat x) in Refl
multAssociative x y (Pos Z) =
  rewrite multZeroRightZero (absSIntNat y) in
    rewrite multZeroRightZero (absSIntNat x) in
      rewrite multZeroRightZero (absSIntNat (ctrSInt (sign x * sign y)
                                                     (absSIntNat x * absSIntNat y))) in
        Refl
multAssociative (Neg x) (Neg y) (Pos z) = ?holeHere 
multAssociative (Neg x) (Pos y) (Neg z) = ?holeHere 
multAssociative (Pos x) (Pos y) (Pos z) = ?holeHere 
multAssociative (Pos x) (Neg y) (Neg z) = ?holeHere 
multAssociative (Neg x) (Neg y) (Neg z) = ?holeHere 
multAssociative (Neg x) (Pos y) (Pos z) = ?holeHere 
multAssociative (Pos x) (Neg y) (Pos z) = ?holeHere 
multAssociative (Pos x) (Pos y) (Neg z) = ?holeHere 
-}

||| Not (yet) implemented because Agda uses a ring solver (+-*-solver) which Idris doesn't have.
||| Frank's work might help here, but I don't know how well that would actually work...
||| Otherwise, will need to do this by hand (later).
|||
||| Note that this currently uses a `believe_me`.
multRightDistribOverPlus : (x,y,z : SInt) -> (y + z) * x = (y * x) + (z * x)
multRightDistribOverPlus x y z = believe_me ()

multLeftDistribOverPlus : (x,y,z : SInt) -> x * (y + z) = (x * y) + (x * z)
multLeftDistribOverPlus x y z =
  rewrite multCommutative x y in
    rewrite multCommutative x z in
      rewrite multCommutative x (y + z) in
        multRightDistribOverPlus x y z
