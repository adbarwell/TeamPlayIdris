module Lang.Semantics

import public IdrisUtils.Equality

import public Lang.Syntax
import public Lang.Context
import public Lang.WellFormedness

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data Groundness : (c : Type) -> (ctx : Ctx c) -> Type where
  Ground : (ok : AllJust ctx) -> Groundness c ctx
  NonGround : (fv : PString) -> (val : c) -> (ok : OneNothing ctx fv) -> Groundness c ctx

data OSAExp : {st  : OrdStruct c}
           -> (e   : AExp st)
           -> (wf  : WFAExp e ctx)
           -> (gnd : Groundness c ctx)
           -> (val : c)
           -> Type where
  SmLit : (x : c) -> OSAExp (TmLit x) WfLit gnd x
  SmAdd : {ok : HasAddition (theStruct st) op}
       -> (x, y : c)
       -> (s1 : OSAExp a1 p gnd x)
       -> (s2 : OSAExp a2 q gnd y)
       -> OSAExp {st} (TmAdd a1 a2) (WfAdd ok p q) gnd (op x y)
  SmSub : {ok : HasSubtraction (theStruct st) op}
       -> (x, y : c)
       -> (s1 : OSAExp a1 p gnd x)
       -> (s2 : OSAExp a2 q gnd y)
       -> OSAExp {st} (TmSub a1 a2) (WfSub ok p q) gnd (op x y)
  SmMul : {ok : HasMultiplication (theStruct st) op}
       -> (x, y : c)
       -> (s1 : OSAExp a1 p gnd x)
       -> (s2 : OSAExp a2 q gnd y)
       -> OSAExp {st} (TmMul a1 a2) (WfMul ok p q) gnd (op x y)
  
  ||| Variables (Ground Case)
  |||
  ||| We know that CtxLookup will always return with a Just because we've a proof that the context
  ||| always contains a value for each entry.
  SmVarG : (x : c)
        -> (ptr : CtxLookup var ok (Just x))
        -> OSAExp (TmVar var) (WfVar ok) (Ground p) x

  ||| Variables (Non-Ground Case)
  |||
  ||| When the given variable is free, we use the given value in the Groundness definition.
  SmVarNGTheVar : (x : c) -> OSAExp (TmVar var) (WfVar ok) (NonGround var x p) x
  ||| Variables (Non-Ground Case)
  |||
  ||| When the given variable has a known value in the context, we know that CtxLookup will return 
  ||| with a Just because we've a proof that the context contains only a single hole (Nothing).
  SmVarNG : (x : c)
         -> (neq : NotEq var fv)
         -> (ptr : CtxLookup var ok (Just x))
         -> OSAExp (TmVar var) (WfVar ok) (NonGround fv y p) x

---------------------------------------------------------------------------------------------------
-- [Covering Function] ----------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

evalAExp : {st : OrdStruct c}
        -> (e : AExp st)
        -> (wf : WFAExp e ctx)
        -> (gnd : Groundness c ctx)
        -> Subset c (OSAExp e wf gnd)
evalAExp (TmLit x) WfLit gnd = Element x (SmLit x)
evalAExp (TmVar v) (WfVar p) (Ground q) with (ctxLookupAllJust v p q)
  evalAExp (TmVar v) (WfVar p) (Ground q) | (x ** r) = Element x (SmVarG x r)
evalAExp (TmVar v) (WfVar p) (NonGround w x q) with (decPEq v w)
  evalAExp (TmVar v) (WfVar p) (NonGround v x q) | Yes Refl = Element x (SmVarNGTheVar x)
  evalAExp (TmVar v) (WfVar p) (NonGround w x q) | No neq with (ctxLookupOneNothing v p q neq)
    evalAExp (TmVar v) (WfVar p) (NonGround w x q) | No neq | (y ** r) =
      Element y (SmVarNG y neq r)
evalAExp (TmAdd a1 a2) (WfAdd {op} ok w1 w2) gnd with (evalAExp a1 w1 gnd, evalAExp a2 w2 gnd)
  evalAExp (TmAdd a1 a2) (WfAdd {op} ok w1 w2) gnd | (Element x p, Element y q) =
    Element (op x y) (SmAdd x y p q)
evalAExp (TmSub a1 a2) (WfSub {op} ok w1 w2) gnd with (evalAExp a1 w1 gnd, evalAExp a2 w2 gnd)
  evalAExp (TmSub a1 a2) (WfSub {op} ok w1 w2) gnd | (Element x p, Element y q) =
    Element (op x y) (SmSub x y p q)
evalAExp (TmMul a1 a2) (WfMul {op} ok w1 w2) gnd with (evalAExp a1 w1 gnd, evalAExp a2 w2 gnd)
  evalAExp (TmMul a1 a2) (WfMul {op} ok w1 w2) gnd | (Element x p, Element y q) =
    Element (op x y) (SmMul x y p q)

