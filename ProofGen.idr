module ProofGen

import public IdrisUtils.Error

import public Lang.OrdRingInteger
import public Lang.Syntax
import public Lang.Context
import public Lang.WellFormedness
import public Lang.Verification

import public Expression

%default total

---------------------------------------------------------------------------------------------------
-- [Linker] ---------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

fromAExp : AExp -> ErrorOr (AExp OrdRingSInt)
fromAExp (Val n TyInt) = Just (TmLit (cast n))
fromAExp (Val n _) =
  Err (StdErr "Support for doubles and other numeric types is not yet implemented.")
fromAExp (Var n TyInt) with (PString.fromString n)
  | Nothing = Err (StdErr ("Can't cast '" ++ n ++ "' to PString; probably missing characters."))
  | Just n' = Just (TmVar n')
fromAExp (Var n _) =
  Err (StdErr "Support for doubles and other numeric types is not yet implemented.")
fromAExp (Add a1 a2) = do
  a1' <- fromAExp a1
  a2' <- fromAExp a2
  Just (TmAdd a1' a2')
fromAExp (Sub a1 a2) = do
  a1' <- fromAExp a1
  a2' <- fromAExp a2
  Just (TmSub a1' a2')
fromAExp (Mul a1 a2) = do
  a1' <- fromAExp a1
  a2' <- fromAExp a2
  Just (TmMul a1' a2')

fromBExp : BExp -> ErrorOr (BExp OrdRingSInt)
fromBExp (Eq a1 a2) = do
  a1' <- fromAExp a1
  a2' <- fromAExp a2
  Just (TmEq a1' a2')
fromBExp (LT a1 a2) = do
  a1' <- fromAExp a1
  a2' <- fromAExp a2
  Just (TmLT a1' a2')
fromBExp (LTE a1 a2) = do
  a1' <- fromAExp a1
  a2' <- fromAExp a2
  Just (TmLTE a1' a2')
fromBExp (GT a1 a2) = do
  a1' <- fromAExp a1
  a2' <- fromAExp a2
  Just (TmLT a2' a1')
fromBExp (GTE a1 a2) = do
  a1' <- fromAExp a1
  a2' <- fromAExp a2
  Just (TmLTE a2' a1')
fromBExp (Not b1) = do
  b1' <- fromBExp b1
  Just (TmNot b1')
fromBExp (And b1 b2) = do
  b1' <- fromBExp b1
  b2' <- fromBExp b2
  Just (TmAnd b1' b2')
fromBExp (Or b1 b2) = do
  b1' <- fromBExp b1
  b2' <- fromBExp b2
  Just (TmOr b1' b2')

fromCtx : Ctx -> ErrorOr (Ctx SInt)
fromCtx (MkCtx xs) =
  case (fromCtx' xs) of
    Err err => Err err
    Just (nxs ** xs') => Just (MkCtx xs' IsValidCtx)
  where
    fromCtx' : List (String, Maybe String, CType)
            -> ErrorOr (nxs : Nat ** Vect nxs (PString, Maybe SInt))
    fromCtx' [] = Just (Z ** [])
    fromCtx' ((x,Just v,TyInt) :: xs)
      -- | No cprf = Err (TyErr cprf)
      -- | Yes (n ** prf) with (fromCtx' xs)
      with (fromCtx' xs)
        | Err err = Err err
        | Just (nxs ** xs') with (PString.fromString x)
          | Nothing =
            Err (StdErr ("Can't cast" ++ x ++ " to PString; probably missing characters."))
          | Just x' = Just (S nxs ** (x',Just (cast v)) :: xs')
    fromCtx' ((x,Nothing,TyInt) :: xs) with (fromCtx' xs)
      | Err err = Err err
      | Just (nxs ** xs') with (PString.fromString x)
        | Nothing =
          Err (StdErr ("Can't cast" ++ x ++ " to PString; probably missing characters."))
        | Just x' = Just (S nxs ** (x',Nothing) :: xs')
    fromCtx' ((x,v,_) :: xs) =
      Err (StdErr "Support for doubles and other numeric types is not yet implemented.")

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
data Result : Type where
  Success : (b0   : Assertion)
         -- IsGround
         -> (ctx0 : Ctx)
         -> (b    : BExp OrdRingSInt)
         -> (ctx  : Ctx SInt)
         -> (wf   : WFBExp b ctx)
         -> (prf  : VerifBExp StrictTotalOrderingSInt b wf gnd)
         -> Result
  ||| For non-ground assertions, we simply report the assertion and that it is well-formed.
  |||
  ||| We avoid, e.g., proving that the assertion holds for all values between the bounds because
  ||| there could be a very great many numbers within the range and this would take a significant
  ||| amount of memory.
  |||
  ||| We do not provide an inductive proof that the assertion holds for all integers between the 
  ||| bounds given because this would require us to generate a function. This would be interestingn 
  ||| in its own right, but is currently left to future work.
  NonGround : (b0  : Assertion)
           -- IsNonGround
           -> (ctx0 : Ctx)
           -> (b    : BExp OrdRingSInt)
           -> (ctx  : Ctx SInt)
           -> (wf   : WFBExp b ctx)
           -> Result

export
implementation Show Result where
  show (Success b0 ctx0 b ctx wf prf) =
    "b0: " ++ show b0 ++ "\nctx0: " ++ show ctx0 ++ "\nprf: " ++ show prf
  show (NonGround b0 ctx0 b ctx wf) =
    "b0: " ++ show b0 ++ "\nctx0: " ++ show ctx0
  -- we don't really care about this, so I'll leave it as a stub for now.
  -- we will ask/expect the programmer to call 'run' in an Idris REPL for the typed output,
  -- and when running from the main, we will output the proof given the actual numbers
  -- I fear that we might need to have a show case for VerifBExp after all, but we can do the bare
  -- minimum and suggest that this is extensible according to user interface preferences (e.g.
  -- what do you show from the proofs?)

---------------------------------------------------------------------------------------------------
-- [The main interface function] ------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- If you run it as an executable, and it doesn't have arguments do this.
-- Conversely, if it has runtime arguments, check and convert the arguments, then run it as though
-- it were a function using those arguments. The runtime arguments will be converted similarly to 
-- how things in a Ctx are; in fact youcould probably just put together a second context and go
-- from there.

||| Only support signed integers for now, but the system is designed to be extensible to other 
||| numeric types.
export
run : Assertion -> Ctx -> ErrorOr Result
run (Ground b0) ctx0 = do
  ctx <- fromCtx ctx0
  b <- fromBExp b0
  case decWFAssertion (Ground b) ctx of
    No nwf => Err (TyErr nwf)
    Yes (WfGround ok wf) =>
      case decAllJust ctx of
        No naj => Err (TyErr naj)
        Yes aj =>
          Just (Success (Ground b0) ctx0 b ctx wf (verifBExp b wf (Ground aj)))
run (NonGround b0 var lb ub) ctx0 = do
  ctx <- fromCtx ctx0
  b <- fromBExp b0
  case PString.fromString var of
    Nothing => Err (TyErr ("run.fromString", var))
    Just fv => case decWFAssertion (NonGround b fv (cast lb) (cast ub)) ctx of
      No nwf => Err (TyErr ("run.decWFAssertion", b, ctx, nwf))
      Yes (WfNonGround ok wf) => Just (NonGround (NonGround b0 var lb ub) ctx0 b ctx wf)


runNG : Assertion -> Ctx -> Integer -> ErrorOr Result
runNG (Ground b0) ctx0 val = run (Ground b0) ctx0
runNG (NonGround b0 var lb ub) ctx0 val = do
  ctx <- fromCtx ctx0
  b <- fromBExp b0
  case PString.fromString var of
    Nothing => Err (TyErr ("run.fromString", var))
    Just fv => case decWFAssertion (NonGround b fv (cast lb) (cast ub)) ctx of
      No nwf => Err (TyErr ("run.decWFAssertion", b, ctx, nwf))
      Yes (WfNonGround ok wf) =>
        Just
          (Success (NonGround b0 var lb ub) ctx0 b ctx wf
                   (verifBExp b wf (NonGround fv (fromIntegerSInt val) ok)))

testAssert1 : Assertion
testAssert1 =
  Ground (LT (Var "loop_time" TyInt) (Mul (Var "upper_bound" TyInt) (Var "factor" TyInt) ))

||| NB the non-ground variable name *must* have the '.minimum' (or equivalent) removed in *both*
||| the `fv` argument and the assertion itself. The context, also.
||| (I could, theoretically do it here, but this seems like it would be easier to do when 
||| generating the Idris files to begin with.)
|||
||| Additionally, note that the variable names shouldn't have their architecture suffixes.
testAssert2 : Assertion
testAssert2 =
  NonGround (LTE (Var "speck_init_sca_time" TyInt) (Add (Add (Var "CSL_SCA_TIME_MEDIUM" TyInt) (Var "speck_init_ngtime" TyInt) ) (Val "100" TyInt))) "speck_init_ngtime" 37 150

testCtx1 : Ctx
testCtx1 =
  MkCtx [("loop_time",Just "43",TyInt),  ("upper_bound",Just "230",TyInt),  ("factor",Just "1",TyInt) ]

testCtx2 : Ctx
testCtx2 =
  MkCtx [("speck_init_sca_time",Just "167",TyInt), ("CSL_SCA_TIME_MEDIUM",Just "30",TyInt), ("speck_init_ngtime", Nothing, TyInt)]

testAssertD13G : Assertion
testAssertD13G =
  Ground (LTE (Var "sec_lvl_time_nodelay" TyInt) (Var "sec_lvl_time_delayed" TyInt))

testCtxD13G : Ctx
testCtxD13G =
  MkCtx [("sec_lvl_time_delayed", Just "60", TyInt), ("sec_lvl_time_nodelay", Just "40", TyInt)]

testAssertD13NG : Assertion
testAssertD13NG =
  NonGround (LT (Add (Var "main_loop_energy" TyInt) (Var "speck_init_ngenergy" TyInt)) (Mul (Var "sca_energy" TyInt) (Var "CSL_ENERGY_BY_LEVEL" TyInt))) "speck_init_ngenergy" 0 439

testCtxD13NG : Ctx
testCtxD13NG =
  MkCtx [("main_loop_energy", Just "100", TyInt),("speck_init_ngenergy", Nothing, TyInt),("sca_energy", Just "45", TyInt),("CSL_ENERGY_BY_LEVEL",Just "12",TyInt)]
