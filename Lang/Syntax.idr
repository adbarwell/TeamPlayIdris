module Lang.Syntax

import public Data.Vect

import public IdrisUtils.Data.String.PString
import public IdrisUtils.Data.Integer.SInt

import public Lang.Structure

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Syntax Definitions] ---------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| Arithmetic Expressions.
data AExp : (st : OrdStruct c) -> Type where
  TmLit : {st : OrdStruct c} -> (n : c) -> AExp st
  TmVar : (var : PString) -> AExp struct
  TmAdd : (a1, a2 : AExp st) -> AExp st
  TmSub : (a1, a2 : AExp st) -> AExp st
  TmMul : (a1, a2 : AExp st) -> AExp st
  
||| Boolean Expressions.
data BExp : (st : OrdStruct c) -> Type where
  TmEq  : (a1, a2 : AExp st) -> BExp st
  TmLT  : (a1, a2 : AExp st) -> BExp st
  TmLTE : (a1, a2 : AExp st) -> BExp st
  TmNot : (b1     : BExp st) -> BExp st
  TmAnd : (b1, b2 : BExp st) -> BExp st
  TmOr  : (b1, b2 : BExp st) -> BExp st

||| CSL Assertions.
data Assertion : (st : OrdStruct c) -> Type where
  Ground : (b1 : BExp st) -> Assertion st
  |||
  ||| @fv the variable whose value is unknown.
  ||| @lb the lower bound for which the assertion holds.
  ||| @ub the upper bound for which the assertion holds.
  NonGround : {st : OrdStruct c}
           -> (b1 : BExp st) -> (fv : PString) -> (lb,ub : SInt) -> Assertion st
          --  -> (b1 : BExp st) -> (ngs : Vect ngs (String, c)) -> Assertion st


---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data IsGround : (x : Assertion st) -> Type where
  ItIsGround : IsGround (Ground b1)

data IsNonGround : (x : Assertion st) -> Type where
  ItIsNonGround : IsNonGround (NonGround b1 fv lb ub)
