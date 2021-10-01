module IdrisUtils.Ord

import public IdrisUtils.OrdS
import public IdrisUtils.Decidability

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

PropEqSetoid : (c : Type) -> (decEq : (x,y : c) -> Dec (x = y)) -> SetoidT c
PropEqSetoid c decEq =
  MkSetoid {c = c} (=) (\l,r => sym {left=l} {right=r}) (\a,b,c => trans {a=a} {b=b} {c=c}) decEq

||| A strict total ordering over a given carrier type where the equivalence relation is
||| propositional equality (=).
record StrictTotalOrdering (c : Type) where
  constructor MkSTOrdering
  decEq : (x,y : c) -> Dec (x = y)
  ordS : StrictTotalOrderingS c (PropEqSetoid c decEq)

---------------------------------------------------------------------------------------------------
-- [Projections] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

proj_LT : StrictTotalOrdering c -> (c -> c -> Type)
proj_LT ord = proj_LT (ordS ord)

proj_Asym : (ord : StrictTotalOrdering c)
         -> ((x,y : c) -> proj_LT ord x y -> Not (proj_LT ord y x))
proj_Asym ord = proj_Asym (ordS ord)

proj_Trans : (ord : StrictTotalOrdering c)
          -> ((x,y,z : c) -> proj_LT ord x y -> proj_LT ord y z -> proj_LT ord x z)
proj_Trans ord = proj_Trans (ordS ord)

proj_Tricho : (ord : StrictTotalOrdering c)
           -> ((x,y : c) -> Trichotomy (PropEqSetoid c (decEq ord)) (proj_LT ord) x y)
proj_Tricho ord = proj_Tricho (ordS ord)

proj_decLT : (ord : StrictTotalOrdering c) -> ((x,y : c) -> Dec (proj_LT ord x y))
proj_decLT ord = proj_decLT (ordS ord)

---------------------------------------------------------------------------------------------------
-- [LTE (Derived)] --------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data LTE : (ord : StrictTotalOrdering c) -> (x : c) -> (y : c) -> Type where
  IsEq : LTE ord x x
  IsLT : (lt : proj_LT ord x y) -> LTE ord x y

proj_LTE : (ord : StrictTotalOrdering c) -> ((x : c) -> (y : c) -> Type)
proj_LTE = LTE

decLTE_gt : (neq : Not (x = y)) -> (gt : Not (proj_LT ord x y)) -> Not (LTE ord x y)
decLTE_gt neq gt IsEq = neq Refl
decLTE_gt neq gt (IsLT lt) = gt lt

decLTE : (ord : StrictTotalOrdering c) -> (x : c) -> (y : c) -> Dec (proj_LTE ord x y)
decLTE ord x y with (decEq ord x y)
  decLTE ord y y | Yes Refl = Yes IsEq
  decLTE ord x y | No  neq  with (proj_decLT ord x y)
    decLTE ord x y | No neq | Yes lt = Yes (IsLT lt)
    decLTE ord x y | No neq | No  gt = No (decLTE_gt neq gt)

---------------------------------------------------------------------------------------------------
-- [Interfaces] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

interface StrictTotalOrder c where
  theOrder : StrictTotalOrdering c

---------------------------------------------------------------------------------------------------
-- [Positive Decidability] ------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

PropLT : (ord : StrictTotalOrdering c)
      -> (x,y : c)
      -> (p_sound : proj_LT ord x y -> Not (LTE ord y x))
      -> (q_sound : LTE ord y x -> Not (proj_LT ord x y))
      -> Prop
PropLT ord x y p_sound q_sound =
  let p = proj_LT ord x y
      q = LTE ord y x
      decP = proj_decLT ord x y
      decQ = decLTE ord y x
  in MkProp p q decP decQ p_sound q_sound

interface StrictTotalOrder c => LTSound c where
  lt_sound  : {x,y : c} -> proj_LT (Ord.theOrder) x y -> Not (LTE (Ord.theOrder) y x)
  gte_sound : {x,y : c} -> LTE (Ord.theOrder) y x -> Not (proj_LT (Ord.theOrder) x y)
  
decPLT : LTSound c => (x,y : c) -> PDec (PropLT Ord.theOrder x y Ord.lt_sound Ord.gte_sound)
decPLT x y with (proj_Tricho Ord.theOrder x y)
  decPLT x y | IsBinR_xRy p nq nr = Yes p
  decPLT x x | IsEq np = No IsEq
  decPLT x y | IsBinR_yRx q np nr = No (IsLT q)


{-
||| Ordering without EQ.
data SOrdering : Type where
  LT : SOrdering
  GT : SOrdering

implementation Uninhabited (Ord.LT = Ord.GT) where
  uninhabited Refl impossible

implementation DecEq SOrdering where
  decEq LT LT = Yes Refl
  decEq GT GT = Yes Refl
  decEq LT GT = No absurd
  decEq GT LT = No (absurd . sym)

||| A strict total ordering for a given type.
data TotalOrdering : (c : Type) -> Type where
  ||| .
  |||
  ||| For completeness, we should have a term that distinguishes `LT` and `(=)`.
  |||
  ||| @LT       <
  ||| @isLT     decision procedure for `LT`
  ||| @sing     for a given `x` and `xs` there is only one proof of `LTE x xs`
  ||| @irrefl   \forall x,y . (x < y) -> y ≠ x
  ||| @antisym  \forall x,y . (x < y) \/ (y < x)
  ||| @decEq    can probably be inferred (i.e. ¬((x < y) \/ (y < x)) -> x = y) but I'm lazy
  MkTotOrd : (LT      : c -> c -> Type)
          -> (isLT    : (x : c) -> (y : c) -> Dec (LT x y))
          -> (sing    : (x : c) -> (y : c) -> (p : LT x y) -> (q : LT x y) -> p = q)
          -> (irrefl  : (x : c) -> (p : LT x x) -> Void)
          -> (antisym : (x : c) -> (y : c) -> (p : LT x y) -> (q : LT y x) -> Void)
          -> (decEq   : (x : c) -> (y : c) -> Dec (x = y))
          -> TotalOrdering c

interface TotalOrder c where
  order : TotalOrdering c

---------------------------------------------------------------------------------------------------
-- [Projection Functions] -------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

proj_LT : TotalOrdering c -> (c -> c -> Type)
proj_LT (MkTotOrd lt _ _ _ _ _) = lt

proj_isLT : (ord : TotalOrdering c) -> ((x : c) -> (y : c) -> Dec (proj_LT ord x y))
proj_isLT (MkTotOrd _ isLT _ _ _ _) = isLT

proj_sing : (ord : TotalOrdering c)
         -> ((x : c) -> (y : c) -> (p : proj_LT ord x y) -> (q : proj_LT ord x y) -> p = q)
proj_sing (MkTotOrd _ _ sing _ _ _) = sing

proj_irrefl : (ord : TotalOrdering c)
           -> ((x : c) -> (p : proj_LT ord x x) -> Void)
proj_irrefl (MkTotOrd _ _ _ irrefl _ _) = irrefl

proj_antisym : (ord : TotalOrdering c)
            -> ((x : c) -> (y : c) -> (p : proj_LT ord x y) -> (q : proj_LT ord y x) -> Void)
proj_antisym (MkTotOrd _ _ _ _ antisym _) = antisym

proj_decEq : (ord : TotalOrdering c) -> ((x : c) -> (y : c) -> Dec (x = y))
proj_decEq (MkTotOrd _ _ _ _ _ decEq) = decEq

---------------------------------------------------------------------------------------------------
-- [LTE (Derived)] --------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data LTE : (ord : TotalOrdering c) -> (x : c) -> (y : c) -> Type where
  IsEq : LTE ord x x
  IsLT : (lt : proj_LT ord x y) -> LTE ord x y

proj_LTE : (ord : TotalOrdering c) -> ((x : c) -> (y : c) -> Type)
proj_LTE = LTE

isLTE_gt : (neq : Not (x = y)) -> (gt : Not (proj_LT ord x y)) -> LTE ord x y -> Void
isLTE_gt neq gt IsEq = neq Refl
isLTE_gt neq gt (IsLT lt) = gt lt

isLTE : (ord : TotalOrdering c) -> (x : c) -> (y : c) -> Dec (proj_LTE ord x y)
isLTE ord x y with (proj_decEq ord x y)
  isLTE ord y y | Yes Refl = Yes IsEq
  isLTE ord x y | No  neq  with (proj_isLT ord x y)
    isLTE ord x y | No neq | Yes lt = Yes (IsLT lt)
    isLTE ord x y | No neq | No  gt = No (isLTE_gt neq gt)

---------------------------------------------------------------------------------------------------
-- [GT (Derived)] ---------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

proj_GT : (ord : TotalOrdering c) -> (x : c) -> (y : c) -> Type
proj_GT ord x y = proj_LT ord y x

isGT : (ord : TotalOrdering c) -> (x : c) -> (y : c) -> Dec (proj_GT ord x y)
isGT ord x y = proj_isLT ord y x

proj_GTE : (ord : TotalOrdering c) -> (x : c) -> (y : c) -> Type
proj_GTE ord x y = proj_LTE ord y x

isGTE : (ord : TotalOrdering c) -> (x : c) -> (y : c) -> Dec (proj_GTE ord x y)
isGTE ord x y = isLTE ord y x
-}
