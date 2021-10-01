module IdrisUtils.Data.Char.PChar

import public Data.Vect

import public IdrisUtils.Data.Char.QChar
import public IdrisUtils.Ord

%default total

---------------------------------------------------------------------------------------------------
-- [Char] -----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
data PChar : Type where
  MkChar : QChar v (k,i) -> PChar

---------------------------------------------------------------------------------------------------
-- [DecEq] ----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
decEqPChar : (x,y : PChar) -> Dec (x = y)
decEqPChar (MkChar x) (MkChar y) with (decEqQChar x y)
  decEqPChar (MkChar x) (MkChar y) | No neq = No (\Refl => neq Refl)
  decEqPChar (MkChar x) (MkChar x) | Yes Refl = Yes Refl

export
implementation DecEq PChar where
  decEq = decEqPChar

---------------------------------------------------------------------------------------------------
-- [Total Ordering] -------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- [Definition] -----------------------------------------------------------------------------------

public export
data LTPChar : (x,y : PChar) -> Type where
  IsLTPChar : (lt : LTQChar x y) -> LTPChar (MkChar x) (MkChar y)

-- [Asymmetry, Transitivity, and Trichotomy] ------------------------------------------------------

export
asymLTPChar : (x,y : PChar) -> (p : LTPChar x y) -> (q : LTPChar y x) -> Void
asymLTPChar (MkChar x) (MkChar y) (IsLTPChar p) (IsLTPChar q) = asymLTQChar x y p q

export
irrLTPChar : (x : PChar) -> (p : LTPChar x x) -> Void
irrLTPChar x p = asymLTPChar x x p p

export
transLTPChar : (x,y,z : PChar) -> LTPChar x y -> LTPChar y z -> LTPChar x z
transLTPChar (MkChar {v = xv} {k = xk} {i = xi} x)
             (MkChar {v = yv} {k = xk} {i = yi} y)
             (MkChar {v = zv} {k = xk} {i = zi} z)
             (IsLTPChar (IsLTNat p)) (IsLTPChar (IsLTNat q)) =
  IsLTPChar (IsLTNat (transLTNat xi yi zi p q))
transLTPChar (MkChar {v = xv} {k = xk} {i = xi} x)
             (MkChar {v = yv} {k = xk} {i = yi} y)
             (MkChar {v = zv} {k = zk} {i = zi} z)
             (IsLTPChar (IsLTNat p)) (IsLTPChar (IsLTCharKind q)) =
  IsLTPChar (IsLTCharKind q)
transLTPChar (MkChar {v = xv} {k = xk} {i = xi} x)
             (MkChar {v = yv} {k = yk} {i = yi} y)
             (MkChar {v = zv} {k = yk} {i = zi} z)
             (IsLTPChar (IsLTCharKind p)) (IsLTPChar (IsLTNat q)) =
  IsLTPChar (IsLTCharKind p)
transLTPChar (MkChar {v = xv} {k = xk} {i = xi} x)
             (MkChar {v = yv} {k = yk} {i = yi} y)
             (MkChar {v = zv} {k = zk} {i = zi} z)
             (IsLTPChar (IsLTCharKind p)) (IsLTPChar (IsLTCharKind q)) =
  IsLTPChar (IsLTCharKind (transLTCharKind xk yk zk p q))

export
contra1 : (neq : Not (xi = yi)) -> Not (MkChar {i = xi} x = MkChar {i = yi} y)
contra1 neq Refl = neq Refl

export
contra2 : (neq : Not (xk = yk)) -> Not (MkChar {k = xk} x = MkChar {k = yk} y)
contra2 neq Refl = neq Refl

export
trichoLTPChar : (x,y : PChar) -> Trichotomy (PropEqSetoid PChar PChar.decEqPChar) LTPChar x y
trichoLTPChar (MkChar {v = xv} {k = xk} {i = xi} x) (MkChar {v = yv} {k = yk} {i = yi} y) =
  case (trichoLTCharKind xk yk) of
    IsEq asym =>
      case trichoLTNat xi yi of
        IsEq asymNat =>
          case lemma_QChar_injective' x y of
            Refl =>
              case lemma_QChar_singleton x y of
                Refl => IsEq (irrLTPChar (MkChar x))
        IsBinR_xRy p nq neq =>
          IsBinR_xRy (IsLTPChar (IsLTNat p))
                     (asymLTPChar (MkChar x) (MkChar y) (IsLTPChar (IsLTNat p)))
                     (\Refl => neq Refl)
        IsBinR_yRx q np neq =>
          IsBinR_yRx (IsLTPChar (IsLTNat q))
                     (asymLTPChar (MkChar y) (MkChar x) (IsLTPChar (IsLTNat q)))
                     (contra1 neq)

    IsBinR_xRy p nq neq =>
      IsBinR_xRy (IsLTPChar (IsLTCharKind p))
                 (asymLTPChar (MkChar x) (MkChar y) (IsLTPChar (IsLTCharKind p)))
                 (contra2 neq)
    IsBinR_yRx q np neq =>
      IsBinR_yRx (IsLTPChar (IsLTCharKind q))
                 (asymLTPChar (MkChar y) (MkChar x) (IsLTPChar (IsLTCharKind q)))
                 (contra2 neq)

-- [Decision Procedure] ---------------------------------------------------------------------------

export
decLTPChar : (x,y : PChar) -> Dec (LTPChar x y)
decLTPChar (MkChar x) (MkChar y) with (decLTQChar x y)
  | No gte = No (\(IsLTPChar lt) => gte lt)
  | Yes lt = Yes (IsLTPChar lt)

-- [Total Ordering (General Setoid)] --------------------------------------------------------------

export
StrictTotalOrderingTPChar : StrictTotalOrderingT PChar (PropEqSetoid PChar PChar.decEqPChar)
StrictTotalOrderingTPChar = MkSTOrderingT LTPChar asymLTPChar transLTPChar trichoLTPChar decLTPChar

-- [Singleton] ------------------------------------------------------------------------------------

export
singLTPChar : (x,y : PChar) -> (p,q : LTPChar x y) -> p = q
singLTPChar (MkChar x) (MkChar y) (IsLTPChar p) (IsLTPChar q) = rewrite singLTQChar x y p q in Refl

-- [Total Ordering with Singleton] ----------------------------------------------------------------

export
StrictTotalOrderingSPChar : StrictTotalOrderingS PChar (PropEqSetoid PChar PChar.decEqPChar)
StrictTotalOrderingSPChar = MkSTOrderingS StrictTotalOrderingTPChar singLTPChar

-- [Total Ordering] -------------------------------------------------------------------------------

export
StrictTotalOrderingPChar : StrictTotalOrdering PChar
StrictTotalOrderingPChar = MkSTOrdering PChar.decEqPChar StrictTotalOrderingSPChar

---------------------------------------------------------------------------------------------------
-- [CharAsNat] ------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
data PCharAsNat : PChar -> Nat -> Type where
  MkPCharAsNat : CharKindAsNat k n -> PCharAsNat (MkChar {k} {i} x) (i + n)

---------------------------------------------------------------------------------------------------
-- [Char Kinds] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
data Minuscule : PChar -> Type where
  IsUndscr : Minuscule (MkChar C_)
  IsMin1st : Minuscule (MkChar {k = Min1st} x)
  IsMin2nd : Minuscule (MkChar {k = Min2nd} x)
  IsMin3rd : Minuscule (MkChar {k = Min3rd} x)

public export
data Majuscule : PChar -> Type where
  IsMaj1st : Majuscule (MkChar {k = Maj1st} x)
  IsMaj2nd : Majuscule (MkChar {k = Maj2nd} x)
  IsMaj3rd : Majuscule (MkChar {k = Maj3rd} x)

public export
data Numeral : PChar -> Type where
  IsNum : Numeral (MkChar {k = Num} x)

public export
data Prime : PChar -> Type where
  IsPri : Prime (MkChar C')
