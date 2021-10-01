module IdrisUtils.Data.String.QString

import public Data.Vect

import public IdrisUtils.Data.Vect.Equality
import public IdrisUtils.Data.Vect.Sum
import public IdrisUtils.Data.Char.PChar
-- import public IdrisUtils.Nat
-- import public IdrisUtils.Equality
-- import public IdrisUtils.Ord

%default total

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
data QString : (str : Vect len Char) -> Type where
  Nil  : QString []
  (::) : QChar c (k,i) -> QString cs -> QString (c :: cs)

---------------------------------------------------------------------------------------------------
-- [Singleton] ------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| If two strings are indexed by the same character list, then those two strings are the same.
|||
||| I.e. (str1 = str2 -> QString str1 = QString str2)
export
lemma_QString_congruent : (x,y : QString str) -> x = y
lemma_QString_congruent Nil Nil = Refl
lemma_QString_congruent ((::) x xs) ((::) y ys) with (lemma_QChar_injective x y)
  lemma_QString_congruent ((::) x xs) ((::) y ys) | Refl with (lemma_QChar_singleton x y)
    lemma_QString_congruent ((::) x xs) ((::) x ys) | Refl | Refl
      with (lemma_QString_congruent xs ys)
        lemma_QString_congruent ((::) x xs) ((::) x xs) | Refl | Refl | Refl = Refl

---------------------------------------------------------------------------------------------------
-- [DecEq] ----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
decEqQString0 : (x,y : QString str) -> Dec (x = y)
decEqQString0 x y = Yes (lemma_QString_congruent x y)

export
implementation DecEq (QString str) where
  decEq = decEqQString0

export
decEqQString : (x : QString v) -> (y : QString w) -> Dec (x = y)
decEqQString {v} {w} x y with (decEqVect v w)
  decEqQString {v} {w} x y | No neq = No (contra neq) where
    contra : {v' : Vect lv Char}
          -> {w' : Vect lw Char}
          -> {x' : QString v'}
          -> {y' : QString w'}
          -> (c1 : Not (v' = w'))
          -> Not (x' = y')
    contra c1 Refl = c1 Refl
  decEqQString {v} {w = v} x y | Yes Refl = Yes (lemma_QString_congruent x y)

---------------------------------------------------------------------------------------------------
-- [Cast] -----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
toString : QString str -> String
toString {str} _ = pack str

export
implementation Cast (QString str) String where
  cast = toString

export
fromString : (str : String) -> Maybe (QString (fromList (unpack str)))
fromString str = fromString' (fromList (unpack str)) where
  fromString' : (cs : Vect len Char) -> Maybe (QString cs)
  fromString' [] = Just Nil
  fromString' (c :: cs) = do
    Element (k,i) x <- fromCharQChar c
    xs <- fromString' cs
    pure ((::) x xs)

---------------------------------------------------------------------------------------------------
-- [Show] -----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
implementation Show (QString str) where
  show = toString

---------------------------------------------------------------------------------------------------
-- [Total Ordering] -------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- [Definition] -----------------------------------------------------------------------------------

public export
data LTQString : (x : QString v) -> (y : QString w) -> Type where
  IsLTQStringNil : LTQString Nil ((::) y ys)
  IsLTQStringChar : (lt : LTQChar x y) -> LTQString ((::) x xs) ((::) y ys)
  IsLTQStringRest : (lt : LTQString xs ys) -> LTQString ((::) x xs) ((::) x ys)

-- [Uninhabited] ----------------------------------------------------------------------------------

export
implementation Uninhabited (LTQString ((::) x xs) Nil) where
  uninhabited IsLTQStringNil impossible
  uninhabited IsLTQStringChar impossible
  uninhabited IsLTQStringRest impossible

-- [Asymmetry, Transitivity, and Trichotomy] ------------------------------------------------------

export
asymLTQString : (x : QString v) -> (y : QString w) -> LTQString x y -> Not (LTQString y x)
asymLTQString Nil ((::) y ys) IsLTQStringNil q = absurd q
asymLTQString ((::) x xs) ((::) y ys) (IsLTQStringChar p) (IsLTQStringChar q) =
  asymLTQChar x y p q
asymLTQString ((::) x xs) ((::) x ys) (IsLTQStringChar p) (IsLTQStringRest q) =
  irrLTQChar x p
asymLTQString ((::) x xs) ((::) x ys) (IsLTQStringRest p) (IsLTQStringChar q) =
  irrLTQChar x q
asymLTQString ((::) x xs) ((::) x ys) (IsLTQStringRest p) (IsLTQStringRest q) =
  asymLTQString xs ys p q

export
irrLTQString : (x : QString v) -> Not (LTQString x x)
irrLTQString x p = asymLTQString x x p p

export
transLTQString : (x : QString v)
              -> (y : QString w)
              -> (z : QString u)
              -> LTQString x y
              -> LTQString y z
              -> LTQString x z
transLTQString Nil ((::) y ys) ((::) z zs) IsLTQStringNil (IsLTQStringChar q) =
  IsLTQStringNil
transLTQString Nil ((::) y ys) ((::) y zs) IsLTQStringNil (IsLTQStringRest q) =
  IsLTQStringNil
transLTQString ((::) x xs) ((::) y ys) ((::) z zs) (IsLTQStringChar p) (IsLTQStringChar q) =
  IsLTQStringChar (transLTQChar x y z p q)
transLTQString ((::) x xs) ((::) y ys) ((::) y zs) (IsLTQStringChar p) (IsLTQStringRest q) = IsLTQStringChar p
transLTQString ((::) x xs) ((::) x ys) ((::) z zs) (IsLTQStringRest p) (IsLTQStringChar q) = IsLTQStringChar q
transLTQString ((::) x xs) ((::) x ys) ((::) x zs) (IsLTQStringRest p) (IsLTQStringRest q) = IsLTQStringRest (transLTQString xs ys zs p q)

||| We note that setoids (in their current incarnation) are homogeneous, which means we can't
||| construct a proof of Trichotomy for QString unless the indices are the same.
export
trichoLTQString : (x,y : QString v) -> Trichotomy (PropEqSetoid (QString v) QString.decEqQString) LTQString x y
trichoLTQString x y with (lemma_QString_congruent x y)
  trichoLTQString x x | Refl = IsEq (irrLTQString x)

-- [Decision Procedure] ---------------------------------------------------------------------------

export
decLTQString : (x : QString v) -> (y : QString w) -> Dec (LTQString x y)
decLTQString Nil Nil = No (irrLTQString Nil)
decLTQString Nil ((::) y ys) = Yes IsLTQStringNil
decLTQString ((::) x xs) Nil = No (asymLTQString Nil ((::) x xs) IsLTQStringNil)
decLTQString ((::) x xs) ((::) y ys) with (trichoLTPChar (MkChar x) (MkChar y))
  decLTQString ((::) x xs) ((::) x ys) | IsEq irr with (decLTQString xs ys)
    decLTQString ((::) x xs) ((::) x ys) | IsEq irr | Yes p =
      Yes (IsLTQStringRest p)
    decLTQString ((::) x xs) ((::) x ys) | IsEq irr | No np =
      No (\prf => case prf of
                    IsLTQStringChar p => irr (IsLTPChar p)
                    IsLTQStringRest p => np p) -- irrLTPChar (MkChar x) p)
  decLTQString ((::) x xs) ((::) y ys) | IsBinR_xRy (IsLTPChar p) nq neq =
    Yes (IsLTQStringChar p)
  decLTQString ((::) x xs) ((::) y ys) | IsBinR_yRx q np neq =
    No (\prf => case prf of
                  IsLTQStringChar p => np (IsLTPChar p)
                  IsLTQStringRest p => neq Refl)

-- [Total Ordering (General Setoid)] --------------------------------------------------------------

export
StrictTotalOrderingTQString : StrictTotalOrderingT (QString v)
                                                   (PropEqSetoid (QString v) QString.decEqQString)
StrictTotalOrderingTQString =
  MkSTOrderingT LTQString asymLTQString transLTQString trichoLTQString decLTQString

-- [Singleton] ------------------------------------------------------------------------------------

export
singLTQString : (x : QString v)
             -> (y : QString w)
             -> (p,q : LTQString x y)
             -> p = q
singLTQString Nil ((::) y ys) IsLTQStringNil IsLTQStringNil = Refl
singLTQString ((::) x xs) ((::) y ys) (IsLTQStringChar p) (IsLTQStringChar q) =
  case (singLTQChar x y p q) of Refl => Refl
singLTQString ((::) x xs) ((::) x ys) (IsLTQStringChar p) (IsLTQStringRest q)
  with (irrLTQChar x p)
    singLTQString ((::) x xs) ((::) x ys) (IsLTQStringChar p) (IsLTQStringRest q) | _
      impossible
singLTQString ((::) x xs) ((::) x ys) (IsLTQStringRest p) (IsLTQStringChar q)
  with (irrLTQChar x q)
    singLTQString ((::) x xs) ((::) x ys) (IsLTQStringRest p) (IsLTQStringChar q) | _
      impossible
singLTQString ((::) x xs) ((::) x ys) (IsLTQStringRest p) (IsLTQStringRest q) =
  case (singLTQString xs ys p q) of Refl => Refl

-- [Total Ordering with Singleton] ----------------------------------------------------------------

export
StrictTotalOrderingSQString : StrictTotalOrderingS (QString v)
                                                   (PropEqSetoid (QString v) QString.decEqQString)
StrictTotalOrderingSQString = MkSTOrderingS StrictTotalOrderingTQString singLTQString

-- [Total Ordering] -------------------------------------------------------------------------------

export
StrictTotalOrderingQString : StrictTotalOrdering (QString v)
StrictTotalOrderingQString = MkSTOrdering QString.decEqQString StrictTotalOrderingSQString
