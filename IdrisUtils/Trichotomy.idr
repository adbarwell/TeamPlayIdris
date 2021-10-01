module IdrisUtils.Trichotomy

import public IdrisUtils.Setoid

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Definition] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| 'A binary relation R on a set X is trichotomous if for all x and y in X, exactly one of
||| xRy, yRx, and x = y holds.'
|||
data Trichotomy : (setoid : SetoidT c) -> (binR : c -> c -> Type) -> (x,y : c) -> Type where
  IsBinR_xRy : {setoid : SetoidT c}
            -> (xRy : binR x y)
            -> (yRx_contra : Not (binR y x))
            -> (xEQy_contra : Not (eqR setoid x y))
            -> Trichotomy setoid binR x y
  IsBinR_yRx : {setoid : SetoidT c}
            -> (yRx : binR y x)
            -> (xRy_contra : Not (binR x y))
            -> (xEQy_contra : Not (eqR setoid x y))
            -> Trichotomy setoid binR x y
  IsEq       : {setoid : SetoidT c}
            -> (asym   : Not (binR x x))
            -> Trichotomy setoid binR x x

---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

