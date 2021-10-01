module Expression

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Syntax Definitions] ---------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| C Types.
data CType : Type where
  ||| Signed Integers
  TyInt   : CType
  ||| Floating point numbers
  TyDouble : CType
  ||| Anything else; not really supported.
  Other : (typeName : String) -> CType

||| A context is a list of triples that map a variable name to a literal value and its type.
||| Literal values are intended to be derived from Chen's instrumentation.
data Ctx : Type where
  ||| Where (var, val, type)
  MkCtx : List (String, Maybe String, CType) -> Ctx

||| Arithmetic expressions
data AExp : Type where
  ||| Literal values (numbers)
  Val : (n : String) -> (type : CType) -> AExp
  ||| Variables
  Var : (var : String) -> (type : CType) -> AExp
  ||| Addition
  Add : (a1 : AExp) -> (a2 : AExp) -> AExp
  ||| Subtraction
  Sub : (a1 : AExp) -> (a2 : AExp) -> AExp
  ||| Multiplication
  Mul : (a1 : AExp) -> (a2 : AExp) -> AExp

||| Boolean Expressions
data BExp : Type where
  ||| Equality
  Eq  : (a1 : AExp) -> (a2 : AExp) -> BExp
  ||| Inequality (less-than-or-equal-to)
  LTE : (a1 : AExp) -> (a2 : AExp) -> BExp
  ||| Inequality (strictly less-than)
  LT  : (a1 : AExp) -> (a2 : AExp) -> BExp
  ||| Inequality (greater-than-or-equal-to)
  GTE : (a1 : AExp) -> (a2 : AExp) -> BExp
  ||| Inequality (strictly greater-than)
  GT  : (a1 : AExp) -> (a2 : AExp) -> BExp
  ||| Negation
  Not : (b1 : BExp) -> BExp
  ||| Conjunction
  And : (b1 : BExp) -> (b2 : BExp) -> BExp
  ||| Disjunction
  Or  : (b1 : BExp) -> (b2 : BExp) -> BExp

||| CSL assertions.
data Assertion : Type where
  Ground : (b : BExp) -> Assertion
  NonGround : (b : BExp) -> (var : String) -> (lb : Integer) -> (ub : Integer) -> Assertion

---------------------------------------------------------------------------------------------------
-- [Implementations] ------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

implementation Show CType where
  show TyInt = "int"
  show TyDouble = "double"
  show (Other ty) = ty

implementation Show Ctx where
  show (MkCtx xs) = show xs

implementation Show AExp where
  show (Val n ty) = "(" ++ n ++ " : " ++ show ty ++ ")"
  show (Var v ty) = "(" ++ v ++ " : " ++ show ty ++ ")"
  show (Add a1 a2) = "(" ++ show a1  ++ " + " ++ show a2 ++ ")"
  show (Sub a1 a2) = "(" ++ show a1  ++ " - " ++ show a2 ++ ")"
  show (Mul a1 a2) = "(" ++ show a1  ++ " * " ++ show a2 ++ ")"

implementation Show BExp where
  show (Eq  a1 a2) = "(" ++ show a1 ++ " = " ++ show a2 ++ ")"
  show (LT  a1 a2) = "(" ++ show a1 ++ " < " ++ show a2 ++ ")"
  show (LTE a1 a2) = "(" ++ show a1 ++ " ≤ " ++ show a2 ++ ")"
  show (GT  a1 a2) = "(" ++ show a1 ++ " > " ++ show a2 ++ ")"
  show (GTE a1 a2) = "(" ++ show a1 ++ " ≥ " ++ show a2 ++ ")"
  show (And b1 b2) = "(" ++ show b1 ++ " && " ++ show b2 ++ ")"
  show (Or  b1 b2) = "(" ++ show b1 ++ " || " ++ show b2 ++ ")"
  show (Not b1)    = "¬" ++ show b1

implementation Show Assertion where
  show (Ground b) = show b
  show (NonGround b var lb ub) =
    "NonGround (" ++ var ++ ", lb: " ++ show lb ++ ", ub : " ++ show ub ++ ")(" ++ show b ++ ")"
