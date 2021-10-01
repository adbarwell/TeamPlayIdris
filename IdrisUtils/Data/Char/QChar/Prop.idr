module IdrisUtils.Data.Char.QChar.Prop

import public IdrisUtils.Data.Char.QChar.Base
import public IdrisUtils.Nat
import public IdrisUtils.Ord

%default total

--------------------------------------------------------------------------------------------------- 
-- [Injectiveness] --------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
lemma_QChar_injective : (x : QChar v i) -> (y : QChar v j) -> i = j
lemma_QChar_injective C_ C_ = Refl
lemma_QChar_injective C' C' = Refl
lemma_QChar_injective Cstop Cstop = Refl
lemma_QChar_injective C0 C0 = Refl
lemma_QChar_injective C1 C1 = Refl
lemma_QChar_injective C2 C2 = Refl
lemma_QChar_injective C3 C3 = Refl
lemma_QChar_injective C4 C4 = Refl
lemma_QChar_injective C5 C5 = Refl
lemma_QChar_injective C6 C6 = Refl
lemma_QChar_injective C7 C7 = Refl
lemma_QChar_injective C8 C8 = Refl
lemma_QChar_injective C9 C9 = Refl
lemma_QChar_injective Ca Ca = Refl
lemma_QChar_injective Cb Cb = Refl
lemma_QChar_injective Cc Cc = Refl
lemma_QChar_injective Cd Cd = Refl
lemma_QChar_injective Ce Ce = Refl
lemma_QChar_injective Cf Cf = Refl
lemma_QChar_injective Cg Cg = Refl
lemma_QChar_injective Ch Ch = Refl
lemma_QChar_injective Ci Ci = Refl
lemma_QChar_injective Cj Cj = Refl
lemma_QChar_injective Ck Ck = Refl
lemma_QChar_injective Cl Cl = Refl
lemma_QChar_injective Cm Cm = Refl
lemma_QChar_injective Cn Cn = Refl
lemma_QChar_injective Co Co = Refl
lemma_QChar_injective Cp Cp = Refl
lemma_QChar_injective Cq Cq = Refl
lemma_QChar_injective Cr Cr = Refl
lemma_QChar_injective Cs Cs = Refl
lemma_QChar_injective Ct Ct = Refl
lemma_QChar_injective Cu Cu = Refl
lemma_QChar_injective Cv Cv = Refl
lemma_QChar_injective Cw Cw = Refl
lemma_QChar_injective Cx Cx = Refl
lemma_QChar_injective Cy Cy = Refl
lemma_QChar_injective Cz Cz = Refl
lemma_QChar_injective CA CA = Refl
lemma_QChar_injective CB CB = Refl
lemma_QChar_injective CC CC = Refl
lemma_QChar_injective CD CD = Refl
lemma_QChar_injective CE CE = Refl
lemma_QChar_injective CF CF = Refl
lemma_QChar_injective CG CG = Refl
lemma_QChar_injective CH CH = Refl
lemma_QChar_injective CI CI = Refl
lemma_QChar_injective CJ CJ = Refl
lemma_QChar_injective CK CK = Refl
lemma_QChar_injective CL CL = Refl
lemma_QChar_injective CM CM = Refl
lemma_QChar_injective CN CN = Refl
lemma_QChar_injective CO CO = Refl
lemma_QChar_injective CP CP = Refl
lemma_QChar_injective CQ CQ = Refl
lemma_QChar_injective CR CR = Refl
lemma_QChar_injective CS CS = Refl
lemma_QChar_injective CT CT = Refl
lemma_QChar_injective CU CU = Refl
lemma_QChar_injective CV CV = Refl
lemma_QChar_injective CW CW = Refl
lemma_QChar_injective CX CX = Refl
lemma_QChar_injective CY CY = Refl
lemma_QChar_injective CZ CZ = Refl

public export
lemma_QChar_injective' : (x : QChar v i) -> (y : QChar w i) -> v = w
lemma_QChar_injective' C_ C_ = Refl
lemma_QChar_injective' C' C' = Refl
lemma_QChar_injective' Cstop Cstop = Refl
lemma_QChar_injective' C0 C0 = Refl
lemma_QChar_injective' C1 C1 = Refl
lemma_QChar_injective' C2 C2 = Refl
lemma_QChar_injective' C3 C3 = Refl
lemma_QChar_injective' C4 C4 = Refl
lemma_QChar_injective' C5 C5 = Refl
lemma_QChar_injective' C6 C6 = Refl
lemma_QChar_injective' C7 C7 = Refl
lemma_QChar_injective' C8 C8 = Refl
lemma_QChar_injective' C9 C9 = Refl
lemma_QChar_injective' Ca Ca = Refl
lemma_QChar_injective' Cb Cb = Refl
lemma_QChar_injective' Cc Cc = Refl
lemma_QChar_injective' Cd Cd = Refl
lemma_QChar_injective' Ce Ce = Refl
lemma_QChar_injective' Cf Cf = Refl
lemma_QChar_injective' Cg Cg = Refl
lemma_QChar_injective' Ch Ch = Refl
lemma_QChar_injective' Ci Ci = Refl
lemma_QChar_injective' Cj Cj = Refl
lemma_QChar_injective' Ck Ck = Refl
lemma_QChar_injective' Cl Cl = Refl
lemma_QChar_injective' Cm Cm = Refl
lemma_QChar_injective' Cn Cn = Refl
lemma_QChar_injective' Co Co = Refl
lemma_QChar_injective' Cp Cp = Refl
lemma_QChar_injective' Cq Cq = Refl
lemma_QChar_injective' Cr Cr = Refl
lemma_QChar_injective' Cs Cs = Refl
lemma_QChar_injective' Ct Ct = Refl
lemma_QChar_injective' Cu Cu = Refl
lemma_QChar_injective' Cv Cv = Refl
lemma_QChar_injective' Cw Cw = Refl
lemma_QChar_injective' Cx Cx = Refl
lemma_QChar_injective' Cy Cy = Refl
lemma_QChar_injective' Cz Cz = Refl
lemma_QChar_injective' CA CA = Refl
lemma_QChar_injective' CB CB = Refl
lemma_QChar_injective' CC CC = Refl
lemma_QChar_injective' CD CD = Refl
lemma_QChar_injective' CE CE = Refl
lemma_QChar_injective' CF CF = Refl
lemma_QChar_injective' CG CG = Refl
lemma_QChar_injective' CH CH = Refl
lemma_QChar_injective' CI CI = Refl
lemma_QChar_injective' CJ CJ = Refl
lemma_QChar_injective' CK CK = Refl
lemma_QChar_injective' CL CL = Refl
lemma_QChar_injective' CM CM = Refl
lemma_QChar_injective' CN CN = Refl
lemma_QChar_injective' CO CO = Refl
lemma_QChar_injective' CP CP = Refl
lemma_QChar_injective' CQ CQ = Refl
lemma_QChar_injective' CR CR = Refl
lemma_QChar_injective' CS CS = Refl
lemma_QChar_injective' CT CT = Refl
lemma_QChar_injective' CU CU = Refl
lemma_QChar_injective' CV CV = Refl
lemma_QChar_injective' CW CW = Refl
lemma_QChar_injective' CX CX = Refl
lemma_QChar_injective' CY CY = Refl
lemma_QChar_injective' CZ CZ = Refl

--------------------------------------------------------------------------------------------------- 
-- [Singleton] ------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
lemma_QChar_singleton : (x : QChar v i) -> (y : QChar v i) -> x = y
lemma_QChar_singleton C_ C_ = Refl
lemma_QChar_singleton C' C' = Refl
lemma_QChar_singleton Cstop Cstop = Refl
lemma_QChar_singleton C0 C0 = Refl
lemma_QChar_singleton C1 C1 = Refl
lemma_QChar_singleton C2 C2 = Refl
lemma_QChar_singleton C3 C3 = Refl
lemma_QChar_singleton C4 C4 = Refl
lemma_QChar_singleton C5 C5 = Refl
lemma_QChar_singleton C6 C6 = Refl
lemma_QChar_singleton C7 C7 = Refl
lemma_QChar_singleton C8 C8 = Refl
lemma_QChar_singleton C9 C9 = Refl
lemma_QChar_singleton Ca Ca = Refl
lemma_QChar_singleton Cb Cb = Refl
lemma_QChar_singleton Cc Cc = Refl
lemma_QChar_singleton Cd Cd = Refl
lemma_QChar_singleton Ce Ce = Refl
lemma_QChar_singleton Cf Cf = Refl
lemma_QChar_singleton Cg Cg = Refl
lemma_QChar_singleton Ch Ch = Refl
lemma_QChar_singleton Ci Ci = Refl
lemma_QChar_singleton Cj Cj = Refl
lemma_QChar_singleton Ck Ck = Refl
lemma_QChar_singleton Cl Cl = Refl
lemma_QChar_singleton Cm Cm = Refl
lemma_QChar_singleton Cn Cn = Refl
lemma_QChar_singleton Co Co = Refl
lemma_QChar_singleton Cp Cp = Refl
lemma_QChar_singleton Cq Cq = Refl
lemma_QChar_singleton Cr Cr = Refl
lemma_QChar_singleton Cs Cs = Refl
lemma_QChar_singleton Ct Ct = Refl
lemma_QChar_singleton Cu Cu = Refl
lemma_QChar_singleton Cv Cv = Refl
lemma_QChar_singleton Cw Cw = Refl
lemma_QChar_singleton Cx Cx = Refl
lemma_QChar_singleton Cy Cy = Refl
lemma_QChar_singleton Cz Cz = Refl
lemma_QChar_singleton CA CA = Refl
lemma_QChar_singleton CB CB = Refl
lemma_QChar_singleton CC CC = Refl
lemma_QChar_singleton CD CD = Refl
lemma_QChar_singleton CE CE = Refl
lemma_QChar_singleton CF CF = Refl
lemma_QChar_singleton CG CG = Refl
lemma_QChar_singleton CH CH = Refl
lemma_QChar_singleton CI CI = Refl
lemma_QChar_singleton CJ CJ = Refl
lemma_QChar_singleton CK CK = Refl
lemma_QChar_singleton CL CL = Refl
lemma_QChar_singleton CM CM = Refl
lemma_QChar_singleton CN CN = Refl
lemma_QChar_singleton CO CO = Refl
lemma_QChar_singleton CP CP = Refl
lemma_QChar_singleton CQ CQ = Refl
lemma_QChar_singleton CR CR = Refl
lemma_QChar_singleton CS CS = Refl
lemma_QChar_singleton CT CT = Refl
lemma_QChar_singleton CU CU = Refl
lemma_QChar_singleton CV CV = Refl
lemma_QChar_singleton CW CW = Refl
lemma_QChar_singleton CX CX = Refl
lemma_QChar_singleton CY CY = Refl
lemma_QChar_singleton CZ CZ = Refl

---------------------------------------------------------------------------------------------------
-- [(Strict) Total Ordering] ----------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- [Definition] -----------------------------------------------------------------------------------

||| x < y
public export
data LTQChar : (x : QChar v i) -> (y : QChar w j) -> Type where
  IsLTNat : {x  : QChar v (k,i)}
         -> {y  : QChar w (k,j)}
         -> (lt : LTNat i j)
         -> LTQChar x y
  IsLTCharKind : {x  : QChar v (kv,i)}
              -> {y  : QChar w (kw,j)}
              -> (lt : LTCharKind kv kw)
              -> LTQChar x y

-- [Asymmetry, Transitivity, and Trichotomy] ------------------------------------------------------

public export
asymLTQChar : (x : QChar v i)
           -> (y : QChar w j)
           -> (p : LTQChar x y)
           -> (q : LTQChar y x)
           -> Void
asymLTQChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTNat q) = asymLTNat i j p q
asymLTQChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind q) = irreflLTCharKind k q
asymLTQChar {i = (k,i)} {j = (k,j)} x y (IsLTCharKind p) (IsLTNat q) = irreflLTCharKind k p
asymLTQChar {i = (kv,i)} {j = (kw,j)} x y (IsLTCharKind p) (IsLTCharKind q) =
  antisymLTCharKind kv kw p q

public export
irrLTQChar : (x : QChar v i) -> Not (LTQChar x x)
irrLTQChar x p = asymLTQChar x x p p

public export
transLTQChar : (x : QChar v i)
            -> (y : QChar w j)
            -> (z : QChar u k)
            -> LTQChar x y
            -> LTQChar y z
            -> LTQChar x z
transLTQChar {i = (xk, xi)} {j = (xk, yi)} {k = (xk, zi)} x y z (IsLTNat p) (IsLTNat q) =
  IsLTNat (transLTNat xi yi zi p q)
transLTQChar {i = (xk, xi)} {j = (xk, yi)} {k = (zk, zi)} x y z (IsLTNat p) (IsLTCharKind q) =
  IsLTCharKind q
transLTQChar {i = (xk, xi)} {j = (yk, yi)} {k = (yk, zi)} x y z (IsLTCharKind p) (IsLTNat q) =
  IsLTCharKind p
transLTQChar {i = (xk, xi)} {j = (yk, yi)} {k = (zk, zi)} x y z (IsLTCharKind p) (IsLTCharKind q) =
  IsLTCharKind (transLTCharKind xk yk zk p q)

||| We note that setoids (in their current incarnation) are homogeneous, which means we can't
||| construct a proof of Trichotomy for QChar unless the indices are the same.
public export
trichoLTQChar : (x, y : QChar v i)
             -> Trichotomy (PropEqSetoid (QChar v i) Base.decEqQChar0) LTQChar x y
trichoLTQChar x y with (lemma_QChar_singleton x y)
  trichoLTQChar x x | Refl = IsEq (irrLTQChar x)

-- [Decision Procedure] ---------------------------------------------------------------------------

public export
decLTQChar_gt : {x   : QChar v (ki, ni)}
            -> {y   : QChar w (kj, nj)}
            -> (gte : Not (LTCharKind ki kj))
            -> (neq : Not (ki = kj))
            -> LTQChar x y
            -> Void
decLTQChar_gt gte neq (IsLTNat lt) = neq Refl
decLTQChar_gt gte neq (IsLTCharKind lt) = gte lt

public export
decLTQChar_neither : {x     : QChar v (ki, ni)}
                 -> {y     : QChar w (kj, nj)}
                 -> (gte_k : Not (LTCharKind ki kj))
                 -> (gte_n : Not (LTNat ni nj))
                 -> LTQChar x y
                 -> Void
decLTQChar_neither gte_k gte_n (IsLTNat lt) = gte_n lt
decLTQChar_neither gte_k gte_n (IsLTCharKind lt) = gte_k lt

public export
decLTQChar : (x : QChar v i) -> (y : QChar w j) -> Dec (LTQChar x y)
decLTQChar {i = (ki,ni)} {j = (kj,nj)} x y with (isLTCharKind ki kj)
  | Yes lt = Yes (IsLTCharKind lt)
  | No gte_k =
    case decEq ki kj of
      No  neq  => No (decLTQChar_gt gte_k neq)
      Yes Refl =>
        case decLTNat ni nj of
          Yes lt    => Yes (IsLTNat lt)
          No  gte_n => No (decLTQChar_neither gte_k gte_n)

-- [Total Ordering (General Setoid)] --------------------------------------------------------------

public export
StrictTotalOrderingTQChar : StrictTotalOrderingT (QChar v i)
                                                (PropEqSetoid (QChar v i) Base.decEqQChar0)
StrictTotalOrderingTQChar = MkSTOrderingT LTQChar asymLTQChar transLTQChar trichoLTQChar decLTQChar

-- [Singleton] ------------------------------------------------------------------------------------

public export
singLTQChar : (x   : QChar v i)
           -> (y   : QChar w j)
           -> (p,q : LTQChar x y)
           -> p = q
singLTQChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTNat q) =
  case singLTNat i j p q of Refl => Refl
singLTQChar {i = (kv,i)} {j = (kw,j)} x y (IsLTCharKind p) (IsLTCharKind q) =
  case singLTCharKind kv kw p q of Refl => Refl
singLTQChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTSymNum) impossible
singLTQChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTSymMin1st) impossible
singLTQChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTSymMin2nd) impossible
singLTQChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTSymMin3rd) impossible
singLTQChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTSymMaj1st) impossible
singLTQChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTSymMaj2nd) impossible
singLTQChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTSymMaj3rd) impossible
singLTQChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTNumMin1st) impossible
singLTQChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTNumMin2nd) impossible
singLTQChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTNumMin3rd) impossible
singLTQChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTNumMaj1st) impossible
singLTQChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTNumMaj2nd) impossible
singLTQChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTNumMaj3rd) impossible
singLTQChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTMin1stMin2nd) impossible
singLTQChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTMin1stMin3rd) impossible
singLTQChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTMin1stMaj1st) impossible
singLTQChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTMin1stMaj2nd) impossible
singLTQChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTMin1stMaj3rd) impossible
singLTQChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTMin2ndMin3rd) impossible
singLTQChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTMin2ndMaj1st) impossible
singLTQChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTMin2ndMaj2nd) impossible
singLTQChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTMin2ndMaj3rd) impossible
singLTQChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTMin3rdMaj1st) impossible
singLTQChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTMin3rdMaj2nd) impossible
singLTQChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTMin3rdMaj3rd) impossible
singLTQChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTMaj1stMaj2nd) impossible
singLTQChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTMaj1stMaj3rd) impossible
singLTQChar {i = (k,i)} {j = (k,j)} x y (IsLTNat p) (IsLTCharKind LTMaj2ndMaj3rd) impossible

-- [Total Ordering with Singleton] ----------------------------------------------------------------

public export
StrictTotalOrderingSQChar : StrictTotalOrderingS (QChar v i)
                                                 (PropEqSetoid (QChar v i) Base.decEqQChar0)
StrictTotalOrderingSQChar = MkSTOrderingS StrictTotalOrderingTQChar singLTQChar

-- [Total Ordering] -------------------------------------------------------------------------------

public export
StrictTotalOrderingQChar : StrictTotalOrdering (QChar v i)
StrictTotalOrderingQChar = MkSTOrdering Base.decEqQChar0 StrictTotalOrderingSQChar
