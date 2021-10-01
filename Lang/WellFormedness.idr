module Lang.WellFormedness

import public Lang.Syntax
import public Lang.Context

%default total
%access public export

{-
  Here, well-formedness means that all variables are bound and either have a value or are
  non-ground.
-}

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data WFAExp : {st : OrdStruct c} -> (e : AExp st) -> (ctx : Ctx c) -> Type where
  WfLit : WFAExp (TmLit n) ctx
  WfVar : (ok : ElemCtx var ctx) -> WFAExp (TmVar var) ctx
  WfAdd : (ok : HasAddition (theStruct st) op)
       -> (p : WFAExp a1 ctx)
       -> (q : WFAExp a2 ctx)
       -> WFAExp {st} (TmAdd a1 a2) ctx
  WfSub : (ok : HasSubtraction (theStruct st) op)
       -> (p : WFAExp a1 ctx)
       -> (q : WFAExp a2 ctx)
       -> WFAExp {st} (TmSub a1 a2) ctx
  WfMul : (ok : HasMultiplication (theStruct st) op)
       -> (p : WFAExp a1 ctx)
       -> (q : WFAExp a2 ctx)
       -> WFAExp {st} (TmMul a1 a2) ctx

data WFBExp : {st : OrdStruct c} -> (e : BExp st) -> (ctx : Ctx c) -> Type where
  WfEq  : (p : WFAExp a1 ctx) -> (q : WFAExp a2 ctx) -> WFBExp (TmEq a1 a2) ctx
  WfLT  : (p : WFAExp a1 ctx) -> (q : WFAExp a2 ctx) -> WFBExp {st} (TmLT a1 a2) ctx
  WfLTE : (p : WFAExp a1 ctx) -> (q : WFAExp a2 ctx) -> WFBExp {st} (TmLTE a1 a2) ctx
  WfNot : (p : WFBExp b1 ctx) -> WFBExp (TmNot b1) ctx
  WfAnd : (p : WFBExp b1 ctx) -> (q : WFBExp b2 ctx) -> WFBExp (TmAnd b1 b2) ctx
  WfOr  : (p : WFBExp b1 ctx) -> (q : WFBExp b2 ctx) -> WFBExp (TmOr b1 b2) ctx

data WFAssertion : {st : OrdStruct c} -> (assn : Assertion st) -> (ctx : Ctx c) -> Type where
  |||
  ||| @allValsKnown all values are known in the context; i.e. there is no element with `Nothing`.
  ||| @p            well-formedness proof of the boolean expression.
  WfGround : (allValsKnown : AllJust ctx) -> (p : WFBExp b1 ctx) -> WFAssertion (Ground b1) ctx
  |||
  ||| @valsOk       all values are known in the context with the exception of a given variable.
  ||| @p            well-formedness proof of the boolean expression.
  WfNonGround : (valsOk : OneNothing ctx fv)
             -> (p : WFBExp b1 ctx)
             -> WFAssertion (NonGround b1 fv lb ub) ctx

---------------------------------------------------------------------------------------------------
-- [Decidability] ---------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

decWFAExp : {st : OrdStruct c} -> (e : AExp st) -> (ctx : Ctx c) -> Dec (WFAExp e ctx)
decWFAExp (TmLit n) ctx = Yes WfLit
decWFAExp (TmVar var) ctx with (decElemCtx var ctx)
  decWFAExp (TmVar var) ctx | Yes ok = Yes (WfVar ok)
  decWFAExp (TmVar var) ctx | No nok = No (\(WfVar ok) => nok ok)
decWFAExp {st} (TmAdd a1 a2) ctx with (decHasAddition (theStruct st))
  decWFAExp {st} (TmAdd a1 a2) ctx | No nok = No (\(WfAdd {op} ok p q) => nok (Element op ok))
  decWFAExp {st} (TmAdd a1 a2) ctx | Yes (Element op ok) with (decWFAExp a1 ctx, decWFAExp a2 ctx)
    decWFAExp {st} (TmAdd a1 a2) ctx | Yes (Element op ok) | (Yes p, Yes q) =
      Yes (WfAdd ok p q)
    decWFAExp {st} (TmAdd a1 a2) ctx | Yes (Element op ok) | (No np, _)     =
      No (\(WfAdd ok p q) => np p)
    decWFAExp {st} (TmAdd a1 a2) ctx | Yes (Element op ok) | (_    , No nq) =
      No (\(WfAdd ok p q) => nq q)
decWFAExp {st} (TmSub a1 a2) ctx with (decHasSubtraction (theStruct st))
  decWFAExp {st} (TmSub a1 a2) ctx | No nok = No (\(WfSub {op} ok p q) => nok (Element op ok))
  decWFAExp {st} (TmSub a1 a2) ctx | Yes (Element op ok) with (decWFAExp a1 ctx, decWFAExp a2 ctx)
    decWFAExp {st} (TmSub a1 a2) ctx | Yes (Element op ok) | (Yes p, Yes q) =
      Yes (WfSub ok p q)
    decWFAExp {st} (TmSub a1 a2) ctx | Yes (Element op ok) | (No np, _)     =
      No (\(WfSub ok p q) => np p)
    decWFAExp {st} (TmSub a1 a2) ctx | Yes (Element op ok) | (_    , No nq) =
      No (\(WfSub ok p q) => nq q)
decWFAExp {st} (TmMul a1 a2) ctx with (decHasMultiplication (theStruct st))
  decWFAExp {st} (TmMul a1 a2) ctx | No nok = No (\(WfMul {op} ok p q) => nok (Element op ok))
  decWFAExp {st} (TmMul a1 a2) ctx | Yes (Element op ok) with (decWFAExp a1 ctx, decWFAExp a2 ctx)
    decWFAExp {st} (TmMul a1 a2) ctx | Yes (Element op ok) | (Yes p, Yes q) =
      Yes (WfMul ok p q)
    decWFAExp {st} (TmMul a1 a2) ctx | Yes (Element op ok) | (No np, _)     =
      No (\(WfMul ok p q) => np p)
    decWFAExp {st} (TmMul a1 a2) ctx | Yes (Element op ok) | (_    , No nq) =
      No (\(WfMul ok p q) => nq q)

decWFBExp : {st : OrdStruct c} -> (e : BExp st) -> (ctx : Ctx c) -> Dec (WFBExp e ctx)
decWFBExp (TmEq a1 a2) ctx with (decWFAExp a1 ctx, decWFAExp a2 ctx)
  decWFBExp (TmEq a1 a2) ctx | (Yes p, Yes q) = Yes (WfEq p q)
  decWFBExp (TmEq a1 a2) ctx | (No np, _)     = No (\(WfEq p q) => np p)
  decWFBExp (TmEq a1 a2) ctx | (_    , No nq) = No (\(WfEq p q) => nq q)
decWFBExp {st} (TmLT a1 a2) ctx with (decWFAExp a1 ctx, decWFAExp a2 ctx)
  decWFBExp {st} (TmLT a1 a2) ctx | (Yes p, Yes q) = Yes (WfLT p q)
  decWFBExp {st} (TmLT a1 a2) ctx | (No np, _)     = No (\(WfLT p q) => np p)
  decWFBExp {st} (TmLT a1 a2) ctx | (_    , No nq) = No (\(WfLT p q) => nq q)
decWFBExp {st} (TmLTE a1 a2) ctx with (decWFAExp a1 ctx, decWFAExp a2 ctx)
  decWFBExp {st} (TmLTE a1 a2) ctx | (Yes p, Yes q) = Yes (WfLTE p q)
  decWFBExp {st} (TmLTE a1 a2) ctx | (No np, _)     = No (\(WfLTE p q) => np p)
  decWFBExp {st} (TmLTE a1 a2) ctx | (_    , No nq) = No (\(WfLTE p q) => nq q)
decWFBExp (TmNot b1) ctx with (decWFBExp b1 ctx)
  decWFBExp (TmNot b1) ctx | (Yes p) = Yes (WfNot p)
  decWFBExp (TmNot b1) ctx | (No np) = No (\(WfNot p) => np p)
decWFBExp (TmAnd b1 b2) ctx with (decWFBExp b1 ctx, decWFBExp b2 ctx)
  decWFBExp (TmAnd b1 b2) ctx | (Yes p, Yes q) = Yes (WfAnd p q)
  decWFBExp (TmAnd b1 b2) ctx | (No np, _)     = No (\(WfAnd p q) => np p)
  decWFBExp (TmAnd b1 b2) ctx | (_    , No nq) = No (\(WfAnd p q) => nq q)
decWFBExp (TmOr b1 b2) ctx with (decWFBExp b1 ctx, decWFBExp b2 ctx)
  decWFBExp (TmOr b1 b2) ctx | (Yes p, Yes q) = Yes (WfOr p q)
  decWFBExp (TmOr b1 b2) ctx | (No np, _)     = No (\(WfOr p q) => np p)
  decWFBExp (TmOr b1 b2) ctx | (_    , No nq) = No (\(WfOr p q) => nq q)

decWFAssertion : {st : OrdStruct c} -> (x : Assertion st) -> (ctx : Ctx c) -> Dec (WFAssertion x ctx)
decWFAssertion (Ground b1) ctx with (decAllJust ctx)
  decWFAssertion (Ground b1) ctx | No nallValsKnown = No (\(WfGround p q) => nallValsKnown p)
  decWFAssertion (Ground b1) ctx | Yes allValsKnown with (decWFBExp b1 ctx)
    decWFAssertion (Ground b1) ctx | Yes allValsKnown | No nq = No (\(WfGround p q) => nq q)
    decWFAssertion (Ground b1) ctx | Yes allValsKnown | Yes q = Yes (WfGround allValsKnown q)
decWFAssertion (NonGround b1 fv lb ub) ctx with (decOneNothing ctx fv)
  decWFAssertion (NonGround b1 fv lb ub) ctx | No nvalsOk = No (\(WfNonGround p q) => nvalsOk p)
  decWFAssertion (NonGround b1 fv lb ub) ctx | Yes valsOk with (decWFBExp b1 ctx)
    decWFAssertion (NonGround b1 fv lb ub) ctx | Yes valsOk | No nq = No (\(WfNonGround p q) => nq q)
    decWFAssertion (NonGround b1 fv lb ub) ctx | Yes valsOk | Yes q = Yes (WfNonGround valsOk q)
