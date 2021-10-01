module Lang.OrdRingInteger

import public IdrisUtils.Data.Integer.SInt
import public IdrisUtils.Equality

import public Lang.Structure

%default total
%access public export

{-
  Signed integers as an Ordered Ring.
-}

---------------------------------------------------------------------------------------------------
-- [Definition] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

MagmaSIntPlus : Magma SInt SInt.plus
MagmaSIntPlus = IsMagma SInt.plus

SemigroupSIntPlus : Semigroup SInt SInt.plus
SemigroupSIntPlus = IsSemigroup MagmaSIntPlus plusAssociative

MonoidSIntPlus : Monoid SInt SInt.plus (Pos Z)
MonoidSIntPlus = IsMonoid SemigroupSIntPlus plusLeftIdentity plusRightIdentity

GroupSIntPlus : Group SInt SInt.plus SInt.negate (Pos Z)
GroupSIntPlus = IsGroup MonoidSIntPlus plusLeftInverse plusRightInverse

AbGroupSIntPlus : AbelianGroup SInt SInt.plus SInt.negate (Pos Z)
AbGroupSIntPlus = IsAbelianGroup GroupSIntPlus plusCommutative

MagmaSIntMult : Magma SInt SInt.mult
MagmaSIntMult = IsMagma SInt.mult

SemigroupSIntMult : Semigroup SInt SInt.mult
SemigroupSIntMult = IsSemigroup MagmaSIntMult multAssociative

MonoidSIntMult : Monoid SInt SInt.mult (Pos (S Z))
MonoidSIntMult = IsMonoid SemigroupSIntMult multLeftIdentity multRightIdentity

RingSInt : Ring SInt SInt.plus SInt.mult SInt.negate (Pos Z) (Pos (S Z))
RingSInt = IsRing AbGroupSIntPlus MonoidSIntMult multLeftDistribOverPlus multRightDistribOverPlus

OrdRingSInt : OrdStruct SInt
OrdRingSInt = MkOrdStruct (MkRing RingSInt) StrictTotalOrderingSInt
