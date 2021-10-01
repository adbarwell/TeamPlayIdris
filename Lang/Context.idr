module Lang.Context

import public Data.Vect

import public IdrisUtils.Data.String.PString
import public IdrisUtils.Equality

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Definition] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data ValidCtx : (ctx : Vect n (PString, Maybe c)) -> Type where
  ||| TODO
  |||
  ||| 1. Uniqueness of variables.
  ||| 2. At most one Nothing.
  IsValidCtx : ValidCtx ctx

||| A context is a mapping of variables (Nat) to values. In the non-ground case, the variable
||| whose value is unknown is represented by `Nothing`.
data Ctx : (c : Type) -> Type where
  MkCtx : (ctx : Vect n (PString, Maybe c)) -> (ok : ValidCtx ctx) -> Ctx c

---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- [Membership] -----------------------------------------------------------------------------------

data ElemFst : (x : c) -> (xs : Vect n (c,c')) -> Type where
  Here  : ElemFst x ((x,y) :: xs)
  There : (later : ElemFst x xs) -> ElemFst x ((y,z) :: xs)

implementation Uninhabited (ElemFst x []) where
  uninhabited Here impossible
  uninhabited There impossible

neitherHereNorThere : (contra1 : Not (x = y))
                   -> (contra2 : Not (ElemFst x xs))
                   -> Not (ElemFst x ((y,z) :: xs))
neitherHereNorThere contra1 contra2 Here = contra1 Refl
neitherHereNorThere contra1 contra2 (There later) = contra2 later

decElemFst : DecEq c => (x : c) -> (xs : Vect n (c,c')) -> Dec (ElemFst x xs)
decElemFst x [] = No absurd
decElemFst x ((y,z) :: xs) with (decEq x y)
  decElemFst x ((x,z) :: xs) | Yes Refl = Yes Here
  decElemFst x ((y,z) :: xs) | No neq with (decElemFst x xs)
    decElemFst x ((y,z) :: xs) | No neq | Yes later = Yes (There later)
    decElemFst x ((y,z) :: xs) | No neq | No nlater = No (neitherHereNorThere neq nlater)

data ElemCtx : (var : PString) -> (ctx : Ctx c) -> Type where
  IsElemCtx : (p : ElemFst var ctx) -> ElemCtx var (MkCtx ctx ok)

decElemCtx : (var : PString) -> (ctx : Ctx c) -> Dec (ElemCtx var ctx)
decElemCtx var (MkCtx ctx ok) with (decElemFst var ctx)
  decElemCtx var (MkCtx ctx ok) | Yes p = Yes (IsElemCtx p)
  decElemCtx var (MkCtx ctx ok) | No np = No (\(IsElemCtx p) => np p)

-- [Contents] -------------------------------------------------------------------------------------

data AllJustCtxVect : (ctx : Vect n (PString, Maybe c)) -> Type where
  VacuousJustCtx : AllJustCtxVect []
  IsAllJustCtxVect : (later : AllJustCtxVect xs) -> AllJustCtxVect ((v, Just n) :: xs)

implementation Uninhabited (AllJustCtxVect ((x,Nothing) :: xs)) where
  uninhabited VacuousJustCtx impossible
  uninhabited IsAllJustCtxVect impossible

data AllJust : (ctx : Ctx c) -> Type where
  IsAllJust : (p : AllJustCtxVect ctx) -> AllJust (MkCtx ctx ok)

decAllJustCtxVect : (ctx : Vect n (PString, Maybe c)) -> Dec (AllJustCtxVect ctx)
decAllJustCtxVect [] = Yes VacuousJustCtx
decAllJustCtxVect ((x,Just y) :: xs) with (decAllJustCtxVect xs)
  decAllJustCtxVect ((x,Just y) :: xs) | Yes later = Yes (IsAllJustCtxVect later)
  decAllJustCtxVect ((x,Just y) :: xs) | No nlater = No (\(IsAllJustCtxVect later) => nlater later)
decAllJustCtxVect ((x,Nothing) :: xs) = No absurd

decAllJust : (ctx : Ctx c) -> Dec (AllJust ctx)
decAllJust (MkCtx ctx ok) with (decAllJustCtxVect ctx)
  decAllJust (MkCtx ctx ok) | Yes p = Yes (IsAllJust p)
  decAllJust (MkCtx ctx ok) | No np = No (\(IsAllJust p) => np p)

data OneNothingCtxVect : (ctx : Vect n (PString, Maybe c)) -> (fv : PString) -> Type where
  HereNothing : (restJust : AllJustCtxVect xs) -> OneNothingCtxVect ((fv,Nothing) :: xs) fv
  ThereNothing : (later : OneNothingCtxVect xs fv) -> OneNothingCtxVect ((x,Just y) :: xs) fv

implementation Uninhabited (OneNothingCtxVect [] fv) where
  uninhabited HereNothing impossible
  uninhabited ThereNothing impossible

data OneNothing : (ctx : Ctx c) -> (fv : PString) -> Type where
  IsOneNothing : (p : OneNothingCtxVect ctx fv) -> OneNothing (MkCtx ctx ok) fv

decOneNothingCtxVect : (ctx : Vect n (PString, Maybe c))
                    -> (fv : PString)
                    -> Dec (OneNothingCtxVect ctx fv)
decOneNothingCtxVect [] fv = No absurd
decOneNothingCtxVect ((x,Nothing) :: xs) fv with (decEq x fv)
  decOneNothingCtxVect ((x,Nothing) :: xs) fv | No neq = No (\(HereNothing p) => neq Refl)
  decOneNothingCtxVect ((fv,Nothing) :: xs) fv | Yes Refl with (decAllJustCtxVect xs)
    decOneNothingCtxVect ((fv,Nothing) :: xs) fv | Yes Refl | Yes restJust =
      Yes (HereNothing restJust)
    decOneNothingCtxVect ((fv,Nothing) :: xs) fv | Yes Refl | No nrestJust =
      No (\(HereNothing p) => nrestJust p)
decOneNothingCtxVect ((x,Just y) :: xs) fv with (decOneNothingCtxVect xs fv)
  decOneNothingCtxVect ((x,Just y) :: xs) fv | No nlater = No (\(ThereNothing p) => nlater p)
  decOneNothingCtxVect ((x,Just y) :: xs) fv | Yes later = Yes (ThereNothing later)

decOneNothing : (ctx : Ctx c) -> (fv : PString) -> Dec (OneNothing ctx fv)
decOneNothing (MkCtx ctx ok) fv with (decOneNothingCtxVect ctx fv)
  decOneNothing (MkCtx ctx ok) fv | No np = No (\(IsOneNothing p) => np p)
  decOneNothing (MkCtx ctx ok) fv | Yes p = Yes (IsOneNothing p)


-- [Value Lookup] ---------------------------------------------------------------------------------

data PairLookup : {xs : Vect n (c,c')} -> (x : c) -> (ok : ElemFst x xs) -> (y : c') -> Type where
  IsHere : PairLookup x (Here {y}) y
  IsThere : (p : PairLookup x later y) -> PairLookup x (There later) y

pairLookup : {xs : Vect n (c,c')} -> (x : c) -> (ok : ElemFst x xs) -> (y : c' ** PairLookup x ok y)
pairLookup x (Here {y}) = (y ** IsHere)
pairLookup x (There later) with (pairLookup x later)
  pairLookup x (There later) | (y ** p) = (y ** IsThere p)

data CtxLookup : {ctx : Ctx c}
              -> (var : PString) -> (ok : ElemCtx var ctx) -> (val : Maybe c) -> Type where
  MkCtxLookup : (p : PairLookup var q val) -> CtxLookup var (IsElemCtx q) val

ctxLookup : {ctx : Ctx c}
         -> (var : PString) -> (ok : ElemCtx var ctx) -> Subset (Maybe c) (CtxLookup var ok)
ctxLookup var (IsElemCtx p) with (pairLookup var p)
  ctxLookup var (IsElemCtx p) | (val ** q) = Element val (MkCtxLookup q)

pairLookupAllJust : {xs : Vect n (PString,Maybe c)}
                 -> (x : PString)
                 -> (p : ElemFst x xs)
                 -> (q : AllJustCtxVect xs)
                 -> (y : c ** PairLookup x p (Just y))
pairLookupAllJust {xs = ((x,Just y) :: xs)} x Here (IsAllJustCtxVect q) = (y ** IsHere)
pairLookupAllJust x (There p) (IsAllJustCtxVect q) with (pairLookupAllJust x p q)
  pairLookupAllJust x (There p) (IsAllJustCtxVect q) | (y ** r) = (y ** IsThere r)

pairLookupOneNothing : {xs : Vect n (PString,Maybe c)}
                    -> (x : PString)
                    -> (p : ElemFst x xs)
                    -> (q : OneNothingCtxVect xs fv)
                    -> (r : NotEq x fv)
                    -> (y : c ** PairLookup x p (Just y))
pairLookupOneNothing {xs = (x,Nothing) :: xs} x Here (HereNothing q) r
  with (lemma_NotEq_irreflexive r)
    pairLookupOneNothing {xs = (x,Nothing) :: xs} x Here (HereNothing q) r | _ impossible
pairLookupOneNothing {xs = (x,Just y) :: xs} x Here (ThereNothing q) r = (y ** IsHere)
pairLookupOneNothing {xs = (fv,Nothing) :: xs} x (There p) (HereNothing q) r
  with (pairLookupAllJust x p q)
    pairLookupOneNothing {xs = (fv,Nothing) :: xs} x (There p) (HereNothing q) r | (y ** s) =
      (y ** IsThere s)
pairLookupOneNothing x (There p) (ThereNothing q) r with (pairLookupOneNothing x p q r)
  pairLookupOneNothing x (There p) (ThereNothing q) r | (y ** s) = (y ** IsThere s)

ctxLookupAllJust : {ctx : Ctx c}
                -> (var : PString)
                -> (p : ElemCtx var ctx)
                -> (q : AllJust ctx)
                -> (x : c ** CtxLookup var p (Just x))
ctxLookupAllJust var (IsElemCtx p) (IsAllJust q) with (pairLookupAllJust var p q)
  ctxLookupAllJust var (IsElemCtx p) (IsAllJust q) | (y ** r) = (y ** MkCtxLookup r)

ctxLookupOneNothing : {ctx : Ctx c}
                   -> (v : PString)
                   -> (p : ElemCtx v ctx)
                   -> (q : OneNothing ctx fv)
                   -> (r : NotEq v fv)
                   -> (x : c ** CtxLookup v p (Just x))
ctxLookupOneNothing v (IsElemCtx p) (IsOneNothing q) r with (pairLookupOneNothing v p q r)
  ctxLookupOneNothing v (IsElemCtx p) (IsOneNothing q) r | (x ** s) = (x ** MkCtxLookup s)

-- [Injectiveness] --------------------------------------------------------------------------------

lemma_PairLookup_injective : (v : c)
                          -> (r : ElemFst v ctx)
                          -> (x : c')
                          -> (p,q : PairLookup v r x)
                          -> p = q
lemma_PairLookup_injective v Here x IsHere IsHere = Refl
lemma_PairLookup_injective v (There r) x (IsThere p) (IsThere q)
  with (lemma_PairLookup_injective v r x p q)
    lemma_PairLookup_injective v (There r) x (IsThere p) (IsThere p) | Refl = Refl

lemma_CtxLookup_injective : (v   : PString)
                         -> (r   : ElemCtx v ctx)
                         -> (x   : Maybe c)
                         -> (p,q : CtxLookup v r x)
                         -> p = q
lemma_CtxLookup_injective v (IsElemCtx r) x (MkCtxLookup p) (MkCtxLookup q)
  with (lemma_PairLookup_injective v r x p q)
    lemma_CtxLookup_injective v (IsElemCtx r) x (MkCtxLookup p) (MkCtxLookup p) | Refl = Refl
