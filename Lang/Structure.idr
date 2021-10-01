module Structure

import public IdrisUtils.Ord

import public Lang.Structure.StructureKind

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data Magma : (c : Type) -> (op : c -> c -> c) -> Type where
  IsMagma : {c : Type} -> (op : c -> c -> c) -> Magma c op

record Semigroup (c : Type) (op : c -> c -> c) where
  constructor IsSemigroup
  isMagma : Magma c op
  opAssociative : (x,y,z : c) -> op (op x y) z = op x (op y z)

record Monoid (c : Type) (op : c -> c -> c) (e : c) where
  constructor IsMonoid
  isSemigroup : Semigroup c op
  opLeftIdentity : (x : c) -> op e x = x
  opRightIdentity : (x : c) -> op x e = x

record Group (c : Type) (op : c -> c -> c) (inverse : c -> c) (e : c) where
  constructor IsGroup
  isMonoid : Monoid c op e
  opLeftInverse : (x : c) -> op x (inverse x) = e
  opRightInverse : (x : c) -> op (inverse x) x = e

record AbelianGroup (c : Type) (op : c -> c -> c) (inverse : c -> c) (e : c) where
  constructor IsAbelianGroup
  isGroup : Group c op inverse e
  opCommutative : (x,y : c) -> op x y = op y x

record Ring (c : Type) (f : c -> c -> c) (g : c -> c -> c) (inverse : c -> c) (i : c) (j : c) where
  constructor IsRing
  isAbelianGroup : AbelianGroup c f inverse i
  isMonoid : Monoid c g j
  leftDistrib : (x,y,z : c) -> g x (f y z) = f (g x y) (g x z)
  rightDistrib : (x,y,z : c) -> g (f y z) x = f (g y x) (g z x)

||| Note that we do assume propositional equality for this. This could cause us to come unstuck
||| with doubles. We could index it by setoid instead.
data Struct : (c : Type) -> Type where
  MkMagma : Magma c op -> Struct c
  MkSemigroup : Semigroup c op -> Struct c
  MkMonoid : Monoid c op e -> Struct c
  MkGroup : Group c op inverse e -> Struct c
  MkAbGroup : AbelianGroup c op inverse e -> Struct c
  MkRing : Ring c f g inverse i j -> Struct c

record OrdStruct (c : Type) where
  constructor MkOrdStruct
  theStruct : Struct c
  theOrder  : StrictTotalOrdering c

---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data HasAddition : (st : Struct c) -> (op : c -> c -> c) -> Type where
  MaAdd : HasAddition (MkMagma (IsMagma op)) op
  SGAdd : HasAddition (MkSemigroup {op} x) op
  MoAdd : HasAddition (MkMonoid {op} x) op
  GrAdd : HasAddition (MkGroup {op} x) op
  AGAdd : HasAddition (MkAbGroup {op} x) op
  RiAdd : HasAddition (MkRing {f = op} x) op

decHasAddition : (st : Struct c) -> Dec (Subset (c -> c -> c) (HasAddition st))
decHasAddition (MkMagma (IsMagma op)) = Yes (Element op MaAdd)
decHasAddition (MkSemigroup {op} x) = Yes (Element op SGAdd)
decHasAddition (MkMonoid {op} x) = Yes (Element op MoAdd)
decHasAddition (MkGroup {op} x) = Yes (Element op GrAdd)
decHasAddition (MkAbGroup {op} x) = Yes (Element op AGAdd)
decHasAddition (MkRing {f = op} x) = Yes (Element op RiAdd)

data HasSubtraction : (st : Struct c) -> (op : c -> c -> c) -> Type where
  GrSub : HasSubtraction (MkGroup {op} {inverse} x) (\a,b => op a (inverse b))
  AGSub : HasSubtraction (MkAbGroup {op} {inverse} x) (\a,b => op a (inverse b))
  RiSub : HasSubtraction (MkRing {f} {inverse} x) (\a,b => f a (inverse b))

decHasSubtraction : (st : Struct c) -> Dec (Subset (c -> c -> c) (HasSubtraction st))
decHasSubtraction (MkMagma (IsMagma op)) = No decHasSubtraction_magma where
  decHasSubtraction_magma : {op : c -> c -> c}
                         -> Not (Subset (c -> c -> c) (HasSubtraction (MkMagma (IsMagma op))))
  decHasSubtraction_magma (Element _ GrSub) impossible
  decHasSubtraction_magma (Element _ AGSub) impossible
  decHasSubtraction_magma (Element _ RiSub) impossible
decHasSubtraction (MkSemigroup {op} x) = No decHasSubtraction_semigroup where
  decHasSubtraction_semigroup : {op : c -> c -> c}
                             -> {x : Semigroup c op}
                             -> Not (Subset (c -> c -> c) (HasSubtraction (MkSemigroup x)))
  decHasSubtraction_semigroup (Element _ GrSub) impossible
  decHasSubtraction_semigroup (Element _ AGSub) impossible
  decHasSubtraction_semigroup (Element _ RiSub) impossible
decHasSubtraction (MkMonoid {op} x) = No decHasSubtraction_monoid where
  decHasSubtraction_monoid : {op : c -> c -> c} -> {x : Monoid c op e}
                          -> Not (Subset (c -> c -> c) (HasSubtraction (MkMonoid x)))
  decHasSubtraction_monoid (Element _ GrSub) impossible
  decHasSubtraction_monoid (Element _ AGSub) impossible
  decHasSubtraction_monoid (Element _ RiSub) impossible
decHasSubtraction (MkGroup {op} {inverse} x) = Yes (Element (\a,b => op a (inverse b)) GrSub)
decHasSubtraction (MkAbGroup {op} {inverse} x) = Yes (Element (\a,b => op a (inverse b)) AGSub)
decHasSubtraction (MkRing {f = op} {inverse} x) = Yes (Element (\a,b => op a (inverse b)) RiSub)

data HasMultiplication : (st : Struct c) -> (op : c -> c -> c) -> Type where
  RiMul : HasMultiplication (MkRing {g} x) g

decHasMultiplication : (st : Struct c) -> Dec (Subset (c -> c -> c) (HasMultiplication st))
decHasMultiplication (MkMagma (IsMagma op)) = No decHasMultiplication_magma where
  decHasMultiplication_magma : {op : c -> c -> c}
                         -> Not (Subset (c -> c -> c) (HasMultiplication (MkMagma (IsMagma op))))
  decHasMultiplication_magma (Element _ RiMul) impossible
decHasMultiplication (MkSemigroup {op} x) = No decHasMultiplication_semigroup where
  decHasMultiplication_semigroup : {op : c -> c -> c}
                             -> {x : Semigroup c op}
                             -> Not (Subset (c -> c -> c) (HasMultiplication (MkSemigroup x)))
  decHasMultiplication_semigroup (Element _ RiMul) impossible
decHasMultiplication (MkMonoid {op} x) = No decHasMultiplication_monoid where
  decHasMultiplication_monoid : {op : c -> c -> c} -> {x : Monoid c op e}
                          -> Not (Subset (c -> c -> c) (HasMultiplication (MkMonoid x)))
  decHasMultiplication_monoid (Element _ RiMul) impossible
decHasMultiplication (MkGroup x) = No decHasMultiplication_group where
  decHasMultiplication_group : {op : c -> c -> c} -> {x : Group c op inverse e}
                            -> Not (Subset (c -> c -> c) (HasMultiplication (MkGroup x)))
  decHasMultiplication_group (Element _ RiMul) impossible
decHasMultiplication (MkAbGroup x) = No decHasMultiplication_abgroup where
  decHasMultiplication_abgroup : {op : c -> c -> c} -> {x : AbelianGroup c op inverse e}
                              -> Not (Subset (c -> c -> c) (HasMultiplication (MkAbGroup x)))
  decHasMultiplication_abgroup (Element _ RiMul) impossible
decHasMultiplication (MkRing {g = op} x) = Yes (Element op RiMul)

{-
  This remains a bit of a hack in re ordering and extensibility, but I'm not going to waste time
  coming up with a new Struct representation.
-

data IsOrdered : Type where
  Yes : IsOrdered
  No  : IsOrdered

ArrStructOps : Type -> StructKind -> Type
ArrStructOps c Magma = (c -> c -> c)
ArrStructOps c Semigroup = (c -> c -> c)
ArrStructOps c Monoid = (c -> c -> c, c)
ArrStructOps c Group = (c -> c -> c, c, c -> c)
ArrStructOps c AbGroup = (c -> c -> c, c, c -> c)
ArrStructOps c Ring = (c -> c -> c, c, c -> c, c -> c -> c, c)

data Struct : (c : Type)
           -> (ord : IsOrdered)
           -> (kind : StructKind)
           -> (ops : ArrStructOps c kind)
           -> Type where
  Magma : (add : c -> c -> c) -> Struct c No Magma add
  Semigroup : (rec : Struct c ord Magma add)
           -> (assoc : (x,y,z : c) -> add (add x y) z = add x (add y z))
           -> Struct c ord Semigroup add
  Monoid : (rec : Struct c ord Semigroup add)
        -> (e  : c)
        -> (eP : (x : c) -> add e x = x)
        -> (eQ : (x : c) -> add x e = x)
        -> Struct c ord Monoid (add, e)
  Group : (rec  : Struct c ord Monoid (add, e))
       -> (inv  : c -> c)
       -> (invP : (x : c) -> add x (inv x) = e)
       -> (invQ : (x : c) -> add (inv x) x = e)
       -> Struct c ord Group (add, e, inv)
  AbGroup : (rec : Struct c ord Group (add,e,inv))
         -> (com : (x,y : c) -> add x y = add y x)
         -> Struct c ord AbGroup (add,e,inv)
  Ring : (rec  : Struct c ord AbGroup (add,e,inv))
      -> (mul  : c -> c -> c)
      -> (f    : c)
      -> (mulM : Struct c ord Monoid (mul,f))
      -> (dstL : (x,y,z : c) -> mul x (add y z) = add (mul x y) (mul x z))
      -> (dstR : (x,y,z : c) -> mul (add y z) x = add (mul y x) (mul z x))
      -> Struct c ord Ring (add, e, inv, mul, f)

  OrdStruct : (rec : Struct c No kind ops)
           -> (ord : StrictTotalOrdering c)
           -> Struct c Yes kind ops

---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data HasOrdering : (kind : Struct c ord kind ops) -> Type where
  MkHasOrdering : HasOrdering (OrdStruct _ _)

---------------------------------------------------------------------------------------------------
-- [Projections] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
-}
