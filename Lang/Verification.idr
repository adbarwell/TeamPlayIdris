module Lang.Verification

import public Lang.Syntax
import public Lang.Context
import public Lang.WellFormedness
import public Lang.Semantics

%default total

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- Why doesn't this mutual block break totality?
-- NB we don't have a proof that True and False are inverses; this is a TODO.

mutual
  public export
  data TrueBExp : {st : OrdStruct c}
              -> (ord : StrictTotalOrdering c)
              -> (e : BExp st)
              -> (wf : WFBExp e ctx)
              -> (gnd : Groundness c ctx)
              -> Type where
    TrEq : (x,y : c)
        -> (r   : OSAExp a1 p gnd x)
        -> (s   : OSAExp a2 q gnd y)
        -> {prf : x = y}
        -> TrueBExp ord (TmEq a1 a2) (WfEq p q) gnd
    TrLT : (x,y : c)
        -> (r   : OSAExp a1 p gnd x)
        -> (s   : OSAExp a2 q gnd y)
        -> {prf : proj_LT ord x y}
        -> TrueBExp ord (TmLT a1 a2) (WfLT p q) gnd
    TrLTE : (x,y : c)
         -> (r   : OSAExp a1 p gnd x)
         -> (s   : OSAExp a2 q gnd y)
         -> {prf : LTE ord x y}
         -> TrueBExp ord (TmLTE a1 a2) (WfLTE p q) gnd
    TrNot : (q : FalseBExp ord b1 p gnd) -> TrueBExp ord (TmNot b1) (WfNot p) gnd
    TrAnd : (r : TrueBExp ord b1 p gnd)
         -> (s : TrueBExp ord b2 q gnd)
         -> TrueBExp ord (TmAnd b1 b2) (WfAnd p q) gnd
    TrOrL : (r : TrueBExp ord b1 p gnd) -> TrueBExp ord (TmOr b1 b2) (WfOr p q) gnd
    TrOrR : (s : TrueBExp ord b2 q gnd) -> TrueBExp ord (TmOr b1 b2) (WfOr p q) gnd

  public export
  data FalseBExp : {st : OrdStruct c}
                -> (ord : StrictTotalOrdering c)
                -> (e : BExp st)
                -> (wf : WFBExp e ctx)
                -> (gnd : Groundness c ctx)
                -> Type where
    FlEq : (x,y : c)
        -> (r   : OSAExp a1 p gnd x)
        -> (s   : OSAExp a2 q gnd y)
        -> {prf : NotEq {ord = ord} x y}
        -> FalseBExp ord (TmEq a1 a2) (WfEq p q) gnd
    FlLT : (x,y : c)
        -> (r   : OSAExp a1 p gnd x)
        -> (s   : OSAExp a2 q gnd y)
        -> {prf : LTE ord y x}
        -> FalseBExp ord (TmLT a1 a2) (WfLT p q) gnd
    FlLTE : (x,y : c)
        -> (r   : OSAExp a1 p gnd x)
        -> (s   : OSAExp a2 q gnd y)
        -> {prf : proj_LT ord y x}
        -> FalseBExp ord (TmLTE a1 a2) (WfLTE p q) gnd
    FlNot : (q : TrueBExp ord b1 p gnd) -> FalseBExp ord (TmNot b1) (WfNot p) gnd 
    FlAndL : (r : FalseBExp ord b1 p gnd) -> FalseBExp ord (TmAnd b1 b2) (WfAnd p q) gnd
    FlAndR : (r : TrueBExp ord b1 p gnd)
          -> (s : FalseBExp ord b2 q gnd)
          -> FalseBExp ord (TmAnd b1 b2) (WfAnd p q) gnd
    FlOr : (r : FalseBExp ord b1 p gnd)
        -> (s : FalseBExp ord b2 q gnd)
        -> FalseBExp ord (TmOr b1 b2) (WfOr p q) gnd

||| In place of Prop, in order to delay the soundness proof obligations. (i.e. P -> ¬Q ^ Q -> ¬P)
public export
data VerifBExp : {st : OrdStruct c}
              -> (ord : StrictTotalOrdering c)
              -> (e : BExp st)
              -> (wf : WFBExp e ctx)
              -> (gnd : Groundness c ctx)
              -> Type where
  True  : (p : TrueBExp ord e wf gnd) -> VerifBExp ord e wf gnd
  False : (q : FalseBExp ord e wf gnd) -> VerifBExp ord e wf gnd

export
verifBExp : LTSound c => {st : OrdStruct c} -- You still need an ordered structure
         -> (e : BExp st)
         -> (wf : WFBExp e ctx)
         -> (gnd : Groundness c ctx)
         -> VerifBExp Ord.theOrder e wf gnd
verifBExp (TmEq a1 a2) (WfEq wf1 wf2) gnd =
  case (evalAExp a1 wf1 gnd, evalAExp a2 wf2 gnd) of
    (Element x p, Element y q) =>
      case decPEq x y of
        Yes eq => True (TrEq x y p q {prf=eq})
        No neq => False (FlEq x y p q {prf=neq})
verifBExp (TmLT a1 a2) (WfLT wf1 wf2) gnd =
  case (evalAExp a1 wf1 gnd, evalAExp a2 wf2 gnd) of
    (Element x p, Element y q) =>
      case decPLT x y of
        Yes lt => True (TrLT x y p q {prf=lt})
        No gte => False (FlLT x y p q {prf=gte})
verifBExp (TmLTE a1 a2) (WfLTE wf1 wf2) gnd =
  case (evalAExp a1 wf1 gnd, evalAExp a2 wf2 gnd) of
    (Element x p, Element y q) =>
      case decPLT y x of
        Yes lt => False (FlLTE x y p q {prf=lt})
        No gte => True (TrLTE x y p q {prf=gte})
verifBExp (TmNot b1) (WfNot wf1) gnd =
  case verifBExp b1 wf1 gnd of
    True p => False (FlNot p)
    False q => True (TrNot q)
verifBExp (TmAnd b1 b2) (WfAnd wf1 wf2) gnd =
  case (verifBExp b1 wf1 gnd, verifBExp b2 wf2 gnd) of
    (True p, True q) => True (TrAnd p q)
    (True p, False q) => False (FlAndR p q)
    (False p, _) => False (FlAndL p)
verifBExp (TmOr b1 b2) (WfOr wf1 wf2) gnd =
  case verifBExp b1 wf1 gnd of
    True p => True (TrOrL p)
    False p =>
      case verifBExp b2 wf2 gnd of
        True q => True (TrOrR q)
        False q => False (FlOr p q)

export 
implementation Show (VerifBExp ord e wf grnd) where
  show (True p) = "True"
  show (False q) = "False"
