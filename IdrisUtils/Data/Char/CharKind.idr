module IdrisUtils.Data.Char.CharKind

import IdrisUtils.Ord

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

{-
  Note to future self: Make it so that the minuscule and majuscule ranks take a natural
  (or a Fin). This will lead to fewer cases in each of the definitions.
-}

data CharKind : Type where
  Sym    : CharKind
  Num    : CharKind
  Min1st : CharKind
  Min2nd : CharKind
  Min3rd : CharKind
  Maj1st : CharKind
  Maj2nd : CharKind
  Maj3rd : CharKind

---------------------------------------------------------------------------------------------------
-- [Relations] ------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data CharKindAsNat : CharKind -> Nat -> Type where
  SymAsNat    : CharKindAsNat Sym Z
  NumAsNat    : CharKindAsNat Num 10
  Min1stAsNat : CharKindAsNat Min1st 20
  Min2ndAsNat : CharKindAsNat Min2nd 30
  Min3rdAsNat : CharKindAsNat Min3rd 40
  Maj1stAsNat : CharKindAsNat Maj1st 50
  Maj2ndAsNat : CharKindAsNat Maj2nd 60
  Maj3rdAsNat : CharKindAsNat Maj3rd 70

charKindAsNat : (k : CharKind) -> Subset Nat (CharKindAsNat k)
charKindAsNat Sym    = Element Z  SymAsNat
charKindAsNat Num    = Element 10 NumAsNat
charKindAsNat Min1st = Element 20 Min1stAsNat
charKindAsNat Min2nd = Element 30 Min2ndAsNat
charKindAsNat Min3rd = Element 40 Min3rdAsNat
charKindAsNat Maj1st = Element 50 Maj1stAsNat
charKindAsNat Maj2nd = Element 60 Maj2ndAsNat
charKindAsNat Maj3rd = Element 70 Maj3rdAsNat

lemma_CharKindAsNat_injection : (p : CharKindAsNat k n) -> (q : CharKindAsNat k m) -> n = m
lemma_CharKindAsNat_injection SymAsNat    SymAsNat    = Refl
lemma_CharKindAsNat_injection NumAsNat    NumAsNat    = Refl
lemma_CharKindAsNat_injection Min1stAsNat Min1stAsNat = Refl
lemma_CharKindAsNat_injection Min2ndAsNat Min2ndAsNat = Refl
lemma_CharKindAsNat_injection Min3rdAsNat Min3rdAsNat = Refl
lemma_CharKindAsNat_injection Maj1stAsNat Maj1stAsNat = Refl
lemma_CharKindAsNat_injection Maj2ndAsNat Maj2ndAsNat = Refl
lemma_CharKindAsNat_injection Maj3rdAsNat Maj3rdAsNat = Refl

lemma_CharKindAsNat_singleton : (p : CharKindAsNat k n) -> (q : CharKindAsNat k n) -> p = q
lemma_CharKindAsNat_singleton SymAsNat    SymAsNat    = Refl
lemma_CharKindAsNat_singleton NumAsNat    NumAsNat    = Refl
lemma_CharKindAsNat_singleton Min1stAsNat Min1stAsNat = Refl
lemma_CharKindAsNat_singleton Min2ndAsNat Min2ndAsNat = Refl
lemma_CharKindAsNat_singleton Min3rdAsNat Min3rdAsNat = Refl
lemma_CharKindAsNat_singleton Maj1stAsNat Maj1stAsNat = Refl
lemma_CharKindAsNat_singleton Maj2ndAsNat Maj2ndAsNat = Refl
lemma_CharKindAsNat_singleton Maj3rdAsNat Maj3rdAsNat = Refl

---------------------------------------------------------------------------------------------------
-- [Total Orders] ---------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data LTCharKind : (x : CharKind) -> (y : CharKind) -> Type where
  LTSymNum       : LTCharKind Sym Num
  LTSymMin1st    : LTCharKind Sym Min1st
  LTSymMin2nd    : LTCharKind Sym Min2nd
  LTSymMin3rd    : LTCharKind Sym Min3rd
  LTSymMaj1st    : LTCharKind Sym Maj1st
  LTSymMaj2nd    : LTCharKind Sym Maj2nd
  LTSymMaj3rd    : LTCharKind Sym Maj3rd
  LTNumMin1st    : LTCharKind Num Min1st
  LTNumMin2nd    : LTCharKind Num Min2nd
  LTNumMin3rd    : LTCharKind Num Min3rd
  LTNumMaj1st    : LTCharKind Num Maj1st
  LTNumMaj2nd    : LTCharKind Num Maj2nd
  LTNumMaj3rd    : LTCharKind Num Maj3rd
  LTMin1stMin2nd : LTCharKind Min1st Min2nd
  LTMin1stMin3rd : LTCharKind Min1st Min3rd
  LTMin1stMaj1st : LTCharKind Min1st Maj1st
  LTMin1stMaj2nd : LTCharKind Min1st Maj2nd
  LTMin1stMaj3rd : LTCharKind Min1st Maj3rd
  LTMin2ndMin3rd : LTCharKind Min2nd Min3rd
  LTMin2ndMaj1st : LTCharKind Min2nd Maj1st
  LTMin2ndMaj2nd : LTCharKind Min2nd Maj2nd
  LTMin2ndMaj3rd : LTCharKind Min2nd Maj3rd
  LTMin3rdMaj1st : LTCharKind Min3rd Maj1st
  LTMin3rdMaj2nd : LTCharKind Min3rd Maj2nd
  LTMin3rdMaj3rd : LTCharKind Min3rd Maj3rd
  LTMaj1stMaj2nd : LTCharKind Maj1st Maj2nd
  LTMaj1stMaj3rd : LTCharKind Maj1st Maj3rd
  LTMaj2ndMaj3rd : LTCharKind Maj2nd Maj3rd

implementation Uninhabited (LTCharKind x x) where
  uninhabited LTSymNum impossible
  uninhabited LTSymMin1st impossible
  uninhabited LTSymMin2nd impossible
  uninhabited LTSymMin3rd impossible
  uninhabited LTSymMaj1st impossible
  uninhabited LTSymMaj2nd impossible
  uninhabited LTSymMaj3rd impossible
  uninhabited LTNumMin1st impossible
  uninhabited LTNumMin2nd impossible
  uninhabited LTNumMin3rd impossible
  uninhabited LTNumMaj1st impossible
  uninhabited LTNumMaj2nd impossible
  uninhabited LTNumMaj3rd impossible
  uninhabited LTMin1stMin2nd impossible
  uninhabited LTMin1stMin3rd impossible
  uninhabited LTMin1stMaj1st impossible
  uninhabited LTMin1stMaj2nd impossible
  uninhabited LTMin1stMaj3rd impossible
  uninhabited LTMin2ndMin3rd impossible
  uninhabited LTMin2ndMaj1st impossible
  uninhabited LTMin2ndMaj2nd impossible
  uninhabited LTMin2ndMaj3rd impossible
  uninhabited LTMin3rdMaj1st impossible
  uninhabited LTMin3rdMaj2nd impossible
  uninhabited LTMin3rdMaj3rd impossible
  uninhabited LTMaj1stMaj2nd impossible
  uninhabited LTMaj1stMaj3rd impossible
  uninhabited LTMaj2ndMaj3rd impossible
implementation Uninhabited (LTCharKind Num    Sym) where
  uninhabited LTSymNum impossible
  uninhabited LTSymMin1st impossible
  uninhabited LTSymMin2nd impossible
  uninhabited LTSymMin3rd impossible
  uninhabited LTSymMaj1st impossible
  uninhabited LTSymMaj2nd impossible
  uninhabited LTSymMaj3rd impossible
  uninhabited LTNumMin1st impossible
  uninhabited LTNumMin2nd impossible
  uninhabited LTNumMin3rd impossible
  uninhabited LTNumMaj1st impossible
  uninhabited LTNumMaj2nd impossible
  uninhabited LTNumMaj3rd impossible
  uninhabited LTMin1stMin2nd impossible
  uninhabited LTMin1stMin3rd impossible
  uninhabited LTMin1stMaj1st impossible
  uninhabited LTMin1stMaj2nd impossible
  uninhabited LTMin1stMaj3rd impossible
  uninhabited LTMin2ndMin3rd impossible
  uninhabited LTMin2ndMaj1st impossible
  uninhabited LTMin2ndMaj2nd impossible
  uninhabited LTMin2ndMaj3rd impossible
  uninhabited LTMin3rdMaj1st impossible
  uninhabited LTMin3rdMaj2nd impossible
  uninhabited LTMin3rdMaj3rd impossible
  uninhabited LTMaj1stMaj2nd impossible
  uninhabited LTMaj1stMaj3rd impossible
  uninhabited LTMaj2ndMaj3rd impossible
implementation Uninhabited (LTCharKind Min1st Sym) where
  uninhabited LTSymNum impossible
  uninhabited LTSymMin1st impossible
  uninhabited LTSymMin2nd impossible
  uninhabited LTSymMin3rd impossible
  uninhabited LTSymMaj1st impossible
  uninhabited LTSymMaj2nd impossible
  uninhabited LTSymMaj3rd impossible
  uninhabited LTNumMin1st impossible
  uninhabited LTNumMin2nd impossible
  uninhabited LTNumMin3rd impossible
  uninhabited LTNumMaj1st impossible
  uninhabited LTNumMaj2nd impossible
  uninhabited LTNumMaj3rd impossible
  uninhabited LTMin1stMin2nd impossible
  uninhabited LTMin1stMin3rd impossible
  uninhabited LTMin1stMaj1st impossible
  uninhabited LTMin1stMaj2nd impossible
  uninhabited LTMin1stMaj3rd impossible
  uninhabited LTMin2ndMin3rd impossible
  uninhabited LTMin2ndMaj1st impossible
  uninhabited LTMin2ndMaj2nd impossible
  uninhabited LTMin2ndMaj3rd impossible
  uninhabited LTMin3rdMaj1st impossible
  uninhabited LTMin3rdMaj2nd impossible
  uninhabited LTMin3rdMaj3rd impossible
  uninhabited LTMaj1stMaj2nd impossible
  uninhabited LTMaj1stMaj3rd impossible
  uninhabited LTMaj2ndMaj3rd impossible
implementation Uninhabited (LTCharKind Min1st Num) where
  uninhabited LTSymNum impossible
  uninhabited LTSymMin1st impossible
  uninhabited LTSymMin2nd impossible
  uninhabited LTSymMin3rd impossible
  uninhabited LTSymMaj1st impossible
  uninhabited LTSymMaj2nd impossible
  uninhabited LTSymMaj3rd impossible
  uninhabited LTNumMin1st impossible
  uninhabited LTNumMin2nd impossible
  uninhabited LTNumMin3rd impossible
  uninhabited LTNumMaj1st impossible
  uninhabited LTNumMaj2nd impossible
  uninhabited LTNumMaj3rd impossible
  uninhabited LTMin1stMin2nd impossible
  uninhabited LTMin1stMin3rd impossible
  uninhabited LTMin1stMaj1st impossible
  uninhabited LTMin1stMaj2nd impossible
  uninhabited LTMin1stMaj3rd impossible
  uninhabited LTMin2ndMin3rd impossible
  uninhabited LTMin2ndMaj1st impossible
  uninhabited LTMin2ndMaj2nd impossible
  uninhabited LTMin2ndMaj3rd impossible
  uninhabited LTMin3rdMaj1st impossible
  uninhabited LTMin3rdMaj2nd impossible
  uninhabited LTMin3rdMaj3rd impossible
  uninhabited LTMaj1stMaj2nd impossible
  uninhabited LTMaj1stMaj3rd impossible
  uninhabited LTMaj2ndMaj3rd impossible
implementation Uninhabited (LTCharKind Min2nd Sym) where
  uninhabited LTSymNum impossible
  uninhabited LTSymMin1st impossible
  uninhabited LTSymMin2nd impossible
  uninhabited LTSymMin3rd impossible
  uninhabited LTSymMaj1st impossible
  uninhabited LTSymMaj2nd impossible
  uninhabited LTSymMaj3rd impossible
  uninhabited LTNumMin1st impossible
  uninhabited LTNumMin2nd impossible
  uninhabited LTNumMin3rd impossible
  uninhabited LTNumMaj1st impossible
  uninhabited LTNumMaj2nd impossible
  uninhabited LTNumMaj3rd impossible
  uninhabited LTMin1stMin2nd impossible
  uninhabited LTMin1stMin3rd impossible
  uninhabited LTMin1stMaj1st impossible
  uninhabited LTMin1stMaj2nd impossible
  uninhabited LTMin1stMaj3rd impossible
  uninhabited LTMin2ndMin3rd impossible
  uninhabited LTMin2ndMaj1st impossible
  uninhabited LTMin2ndMaj2nd impossible
  uninhabited LTMin2ndMaj3rd impossible
  uninhabited LTMin3rdMaj1st impossible
  uninhabited LTMin3rdMaj2nd impossible
  uninhabited LTMin3rdMaj3rd impossible
  uninhabited LTMaj1stMaj2nd impossible
  uninhabited LTMaj1stMaj3rd impossible
  uninhabited LTMaj2ndMaj3rd impossible
implementation Uninhabited (LTCharKind Min2nd Num) where
  uninhabited LTSymNum impossible
  uninhabited LTSymMin1st impossible
  uninhabited LTSymMin2nd impossible
  uninhabited LTSymMin3rd impossible
  uninhabited LTSymMaj1st impossible
  uninhabited LTSymMaj2nd impossible
  uninhabited LTSymMaj3rd impossible
  uninhabited LTNumMin1st impossible
  uninhabited LTNumMin2nd impossible
  uninhabited LTNumMin3rd impossible
  uninhabited LTNumMaj1st impossible
  uninhabited LTNumMaj2nd impossible
  uninhabited LTNumMaj3rd impossible
  uninhabited LTMin1stMin2nd impossible
  uninhabited LTMin1stMin3rd impossible
  uninhabited LTMin1stMaj1st impossible
  uninhabited LTMin1stMaj2nd impossible
  uninhabited LTMin1stMaj3rd impossible
  uninhabited LTMin2ndMin3rd impossible
  uninhabited LTMin2ndMaj1st impossible
  uninhabited LTMin2ndMaj2nd impossible
  uninhabited LTMin2ndMaj3rd impossible
  uninhabited LTMin3rdMaj1st impossible
  uninhabited LTMin3rdMaj2nd impossible
  uninhabited LTMin3rdMaj3rd impossible
  uninhabited LTMaj1stMaj2nd impossible
  uninhabited LTMaj1stMaj3rd impossible
  uninhabited LTMaj2ndMaj3rd impossible
implementation Uninhabited (LTCharKind Min2nd Min1st) where
  uninhabited LTSymNum impossible
  uninhabited LTSymMin1st impossible
  uninhabited LTSymMin2nd impossible
  uninhabited LTSymMin3rd impossible
  uninhabited LTSymMaj1st impossible
  uninhabited LTSymMaj2nd impossible
  uninhabited LTSymMaj3rd impossible
  uninhabited LTNumMin1st impossible
  uninhabited LTNumMin2nd impossible
  uninhabited LTNumMin3rd impossible
  uninhabited LTNumMaj1st impossible
  uninhabited LTNumMaj2nd impossible
  uninhabited LTNumMaj3rd impossible
  uninhabited LTMin1stMin2nd impossible
  uninhabited LTMin1stMin3rd impossible
  uninhabited LTMin1stMaj1st impossible
  uninhabited LTMin1stMaj2nd impossible
  uninhabited LTMin1stMaj3rd impossible
  uninhabited LTMin2ndMin3rd impossible
  uninhabited LTMin2ndMaj1st impossible
  uninhabited LTMin2ndMaj2nd impossible
  uninhabited LTMin2ndMaj3rd impossible
  uninhabited LTMin3rdMaj1st impossible
  uninhabited LTMin3rdMaj2nd impossible
  uninhabited LTMin3rdMaj3rd impossible
  uninhabited LTMaj1stMaj2nd impossible
  uninhabited LTMaj1stMaj3rd impossible
  uninhabited LTMaj2ndMaj3rd impossible
implementation Uninhabited (LTCharKind Min3rd Sym) where
  uninhabited LTSymNum impossible
  uninhabited LTSymMin1st impossible
  uninhabited LTSymMin2nd impossible
  uninhabited LTSymMin3rd impossible
  uninhabited LTSymMaj1st impossible
  uninhabited LTSymMaj2nd impossible
  uninhabited LTSymMaj3rd impossible
  uninhabited LTNumMin1st impossible
  uninhabited LTNumMin2nd impossible
  uninhabited LTNumMin3rd impossible
  uninhabited LTNumMaj1st impossible
  uninhabited LTNumMaj2nd impossible
  uninhabited LTNumMaj3rd impossible
  uninhabited LTMin1stMin2nd impossible
  uninhabited LTMin1stMin3rd impossible
  uninhabited LTMin1stMaj1st impossible
  uninhabited LTMin1stMaj2nd impossible
  uninhabited LTMin1stMaj3rd impossible
  uninhabited LTMin2ndMin3rd impossible
  uninhabited LTMin2ndMaj1st impossible
  uninhabited LTMin2ndMaj2nd impossible
  uninhabited LTMin2ndMaj3rd impossible
  uninhabited LTMin3rdMaj1st impossible
  uninhabited LTMin3rdMaj2nd impossible
  uninhabited LTMin3rdMaj3rd impossible
  uninhabited LTMaj1stMaj2nd impossible
  uninhabited LTMaj1stMaj3rd impossible
  uninhabited LTMaj2ndMaj3rd impossible
implementation Uninhabited (LTCharKind Min3rd Num) where
  uninhabited LTSymNum impossible
  uninhabited LTSymMin1st impossible
  uninhabited LTSymMin2nd impossible
  uninhabited LTSymMin3rd impossible
  uninhabited LTSymMaj1st impossible
  uninhabited LTSymMaj2nd impossible
  uninhabited LTSymMaj3rd impossible
  uninhabited LTNumMin1st impossible
  uninhabited LTNumMin2nd impossible
  uninhabited LTNumMin3rd impossible
  uninhabited LTNumMaj1st impossible
  uninhabited LTNumMaj2nd impossible
  uninhabited LTNumMaj3rd impossible
  uninhabited LTMin1stMin2nd impossible
  uninhabited LTMin1stMin3rd impossible
  uninhabited LTMin1stMaj1st impossible
  uninhabited LTMin1stMaj2nd impossible
  uninhabited LTMin1stMaj3rd impossible
  uninhabited LTMin2ndMin3rd impossible
  uninhabited LTMin2ndMaj1st impossible
  uninhabited LTMin2ndMaj2nd impossible
  uninhabited LTMin2ndMaj3rd impossible
  uninhabited LTMin3rdMaj1st impossible
  uninhabited LTMin3rdMaj2nd impossible
  uninhabited LTMin3rdMaj3rd impossible
  uninhabited LTMaj1stMaj2nd impossible
  uninhabited LTMaj1stMaj3rd impossible
  uninhabited LTMaj2ndMaj3rd impossible
implementation Uninhabited (LTCharKind Min3rd Min1st) where
  uninhabited LTSymNum impossible
  uninhabited LTSymMin1st impossible
  uninhabited LTSymMin2nd impossible
  uninhabited LTSymMin3rd impossible
  uninhabited LTSymMaj1st impossible
  uninhabited LTSymMaj2nd impossible
  uninhabited LTSymMaj3rd impossible
  uninhabited LTNumMin1st impossible
  uninhabited LTNumMin2nd impossible
  uninhabited LTNumMin3rd impossible
  uninhabited LTNumMaj1st impossible
  uninhabited LTNumMaj2nd impossible
  uninhabited LTNumMaj3rd impossible
  uninhabited LTMin1stMin2nd impossible
  uninhabited LTMin1stMin3rd impossible
  uninhabited LTMin1stMaj1st impossible
  uninhabited LTMin1stMaj2nd impossible
  uninhabited LTMin1stMaj3rd impossible
  uninhabited LTMin2ndMin3rd impossible
  uninhabited LTMin2ndMaj1st impossible
  uninhabited LTMin2ndMaj2nd impossible
  uninhabited LTMin2ndMaj3rd impossible
  uninhabited LTMin3rdMaj1st impossible
  uninhabited LTMin3rdMaj2nd impossible
  uninhabited LTMin3rdMaj3rd impossible
  uninhabited LTMaj1stMaj2nd impossible
  uninhabited LTMaj1stMaj3rd impossible
  uninhabited LTMaj2ndMaj3rd impossible
implementation Uninhabited (LTCharKind Min3rd Min2nd) where
  uninhabited LTSymNum impossible
  uninhabited LTSymMin1st impossible
  uninhabited LTSymMin2nd impossible
  uninhabited LTSymMin3rd impossible
  uninhabited LTSymMaj1st impossible
  uninhabited LTSymMaj2nd impossible
  uninhabited LTSymMaj3rd impossible
  uninhabited LTNumMin1st impossible
  uninhabited LTNumMin2nd impossible
  uninhabited LTNumMin3rd impossible
  uninhabited LTNumMaj1st impossible
  uninhabited LTNumMaj2nd impossible
  uninhabited LTNumMaj3rd impossible
  uninhabited LTMin1stMin2nd impossible
  uninhabited LTMin1stMin3rd impossible
  uninhabited LTMin1stMaj1st impossible
  uninhabited LTMin1stMaj2nd impossible
  uninhabited LTMin1stMaj3rd impossible
  uninhabited LTMin2ndMin3rd impossible
  uninhabited LTMin2ndMaj1st impossible
  uninhabited LTMin2ndMaj2nd impossible
  uninhabited LTMin2ndMaj3rd impossible
  uninhabited LTMin3rdMaj1st impossible
  uninhabited LTMin3rdMaj2nd impossible
  uninhabited LTMin3rdMaj3rd impossible
  uninhabited LTMaj1stMaj2nd impossible
  uninhabited LTMaj1stMaj3rd impossible
  uninhabited LTMaj2ndMaj3rd impossible
implementation Uninhabited (LTCharKind Maj1st Sym) where
  uninhabited LTSymNum impossible
  uninhabited LTSymMin1st impossible
  uninhabited LTSymMin2nd impossible
  uninhabited LTSymMin3rd impossible
  uninhabited LTSymMaj1st impossible
  uninhabited LTSymMaj2nd impossible
  uninhabited LTSymMaj3rd impossible
  uninhabited LTNumMin1st impossible
  uninhabited LTNumMin2nd impossible
  uninhabited LTNumMin3rd impossible
  uninhabited LTNumMaj1st impossible
  uninhabited LTNumMaj2nd impossible
  uninhabited LTNumMaj3rd impossible
  uninhabited LTMin1stMin2nd impossible
  uninhabited LTMin1stMin3rd impossible
  uninhabited LTMin1stMaj1st impossible
  uninhabited LTMin1stMaj2nd impossible
  uninhabited LTMin1stMaj3rd impossible
  uninhabited LTMin2ndMin3rd impossible
  uninhabited LTMin2ndMaj1st impossible
  uninhabited LTMin2ndMaj2nd impossible
  uninhabited LTMin2ndMaj3rd impossible
  uninhabited LTMin3rdMaj1st impossible
  uninhabited LTMin3rdMaj2nd impossible
  uninhabited LTMin3rdMaj3rd impossible
  uninhabited LTMaj1stMaj2nd impossible
  uninhabited LTMaj1stMaj3rd impossible
  uninhabited LTMaj2ndMaj3rd impossible
implementation Uninhabited (LTCharKind Maj1st Num) where
  uninhabited LTSymNum impossible
  uninhabited LTSymMin1st impossible
  uninhabited LTSymMin2nd impossible
  uninhabited LTSymMin3rd impossible
  uninhabited LTSymMaj1st impossible
  uninhabited LTSymMaj2nd impossible
  uninhabited LTSymMaj3rd impossible
  uninhabited LTNumMin1st impossible
  uninhabited LTNumMin2nd impossible
  uninhabited LTNumMin3rd impossible
  uninhabited LTNumMaj1st impossible
  uninhabited LTNumMaj2nd impossible
  uninhabited LTNumMaj3rd impossible
  uninhabited LTMin1stMin2nd impossible
  uninhabited LTMin1stMin3rd impossible
  uninhabited LTMin1stMaj1st impossible
  uninhabited LTMin1stMaj2nd impossible
  uninhabited LTMin1stMaj3rd impossible
  uninhabited LTMin2ndMin3rd impossible
  uninhabited LTMin2ndMaj1st impossible
  uninhabited LTMin2ndMaj2nd impossible
  uninhabited LTMin2ndMaj3rd impossible
  uninhabited LTMin3rdMaj1st impossible
  uninhabited LTMin3rdMaj2nd impossible
  uninhabited LTMin3rdMaj3rd impossible
  uninhabited LTMaj1stMaj2nd impossible
  uninhabited LTMaj1stMaj3rd impossible
  uninhabited LTMaj2ndMaj3rd impossible
implementation Uninhabited (LTCharKind Maj1st Min1st) where
  uninhabited LTSymNum impossible
  uninhabited LTSymMin1st impossible
  uninhabited LTSymMin2nd impossible
  uninhabited LTSymMin3rd impossible
  uninhabited LTSymMaj1st impossible
  uninhabited LTSymMaj2nd impossible
  uninhabited LTSymMaj3rd impossible
  uninhabited LTNumMin1st impossible
  uninhabited LTNumMin2nd impossible
  uninhabited LTNumMin3rd impossible
  uninhabited LTNumMaj1st impossible
  uninhabited LTNumMaj2nd impossible
  uninhabited LTNumMaj3rd impossible
  uninhabited LTMin1stMin2nd impossible
  uninhabited LTMin1stMin3rd impossible
  uninhabited LTMin1stMaj1st impossible
  uninhabited LTMin1stMaj2nd impossible
  uninhabited LTMin1stMaj3rd impossible
  uninhabited LTMin2ndMin3rd impossible
  uninhabited LTMin2ndMaj1st impossible
  uninhabited LTMin2ndMaj2nd impossible
  uninhabited LTMin2ndMaj3rd impossible
  uninhabited LTMin3rdMaj1st impossible
  uninhabited LTMin3rdMaj2nd impossible
  uninhabited LTMin3rdMaj3rd impossible
  uninhabited LTMaj1stMaj2nd impossible
  uninhabited LTMaj1stMaj3rd impossible
  uninhabited LTMaj2ndMaj3rd impossible
implementation Uninhabited (LTCharKind Maj1st Min2nd) where
  uninhabited LTSymNum impossible
  uninhabited LTSymMin1st impossible
  uninhabited LTSymMin2nd impossible
  uninhabited LTSymMin3rd impossible
  uninhabited LTSymMaj1st impossible
  uninhabited LTSymMaj2nd impossible
  uninhabited LTSymMaj3rd impossible
  uninhabited LTNumMin1st impossible
  uninhabited LTNumMin2nd impossible
  uninhabited LTNumMin3rd impossible
  uninhabited LTNumMaj1st impossible
  uninhabited LTNumMaj2nd impossible
  uninhabited LTNumMaj3rd impossible
  uninhabited LTMin1stMin2nd impossible
  uninhabited LTMin1stMin3rd impossible
  uninhabited LTMin1stMaj1st impossible
  uninhabited LTMin1stMaj2nd impossible
  uninhabited LTMin1stMaj3rd impossible
  uninhabited LTMin2ndMin3rd impossible
  uninhabited LTMin2ndMaj1st impossible
  uninhabited LTMin2ndMaj2nd impossible
  uninhabited LTMin2ndMaj3rd impossible
  uninhabited LTMin3rdMaj1st impossible
  uninhabited LTMin3rdMaj2nd impossible
  uninhabited LTMin3rdMaj3rd impossible
  uninhabited LTMaj1stMaj2nd impossible
  uninhabited LTMaj1stMaj3rd impossible
  uninhabited LTMaj2ndMaj3rd impossible
implementation Uninhabited (LTCharKind Maj1st Min3rd) where
  uninhabited LTSymNum impossible
  uninhabited LTSymMin1st impossible
  uninhabited LTSymMin2nd impossible
  uninhabited LTSymMin3rd impossible
  uninhabited LTSymMaj1st impossible
  uninhabited LTSymMaj2nd impossible
  uninhabited LTSymMaj3rd impossible
  uninhabited LTNumMin1st impossible
  uninhabited LTNumMin2nd impossible
  uninhabited LTNumMin3rd impossible
  uninhabited LTNumMaj1st impossible
  uninhabited LTNumMaj2nd impossible
  uninhabited LTNumMaj3rd impossible
  uninhabited LTMin1stMin2nd impossible
  uninhabited LTMin1stMin3rd impossible
  uninhabited LTMin1stMaj1st impossible
  uninhabited LTMin1stMaj2nd impossible
  uninhabited LTMin1stMaj3rd impossible
  uninhabited LTMin2ndMin3rd impossible
  uninhabited LTMin2ndMaj1st impossible
  uninhabited LTMin2ndMaj2nd impossible
  uninhabited LTMin2ndMaj3rd impossible
  uninhabited LTMin3rdMaj1st impossible
  uninhabited LTMin3rdMaj2nd impossible
  uninhabited LTMin3rdMaj3rd impossible
  uninhabited LTMaj1stMaj2nd impossible
  uninhabited LTMaj1stMaj3rd impossible
  uninhabited LTMaj2ndMaj3rd impossible
implementation Uninhabited (LTCharKind Maj2nd Sym) where
  uninhabited LTSymNum impossible
  uninhabited LTSymMin1st impossible
  uninhabited LTSymMin2nd impossible
  uninhabited LTSymMin3rd impossible
  uninhabited LTSymMaj1st impossible
  uninhabited LTSymMaj2nd impossible
  uninhabited LTSymMaj3rd impossible
  uninhabited LTNumMin1st impossible
  uninhabited LTNumMin2nd impossible
  uninhabited LTNumMin3rd impossible
  uninhabited LTNumMaj1st impossible
  uninhabited LTNumMaj2nd impossible
  uninhabited LTNumMaj3rd impossible
  uninhabited LTMin1stMin2nd impossible
  uninhabited LTMin1stMin3rd impossible
  uninhabited LTMin1stMaj1st impossible
  uninhabited LTMin1stMaj2nd impossible
  uninhabited LTMin1stMaj3rd impossible
  uninhabited LTMin2ndMin3rd impossible
  uninhabited LTMin2ndMaj1st impossible
  uninhabited LTMin2ndMaj2nd impossible
  uninhabited LTMin2ndMaj3rd impossible
  uninhabited LTMin3rdMaj1st impossible
  uninhabited LTMin3rdMaj2nd impossible
  uninhabited LTMin3rdMaj3rd impossible
  uninhabited LTMaj1stMaj2nd impossible
  uninhabited LTMaj1stMaj3rd impossible
  uninhabited LTMaj2ndMaj3rd impossible
implementation Uninhabited (LTCharKind Maj2nd Num) where
  uninhabited LTSymNum impossible
  uninhabited LTSymMin1st impossible
  uninhabited LTSymMin2nd impossible
  uninhabited LTSymMin3rd impossible
  uninhabited LTSymMaj1st impossible
  uninhabited LTSymMaj2nd impossible
  uninhabited LTSymMaj3rd impossible
  uninhabited LTNumMin1st impossible
  uninhabited LTNumMin2nd impossible
  uninhabited LTNumMin3rd impossible
  uninhabited LTNumMaj1st impossible
  uninhabited LTNumMaj2nd impossible
  uninhabited LTNumMaj3rd impossible
  uninhabited LTMin1stMin2nd impossible
  uninhabited LTMin1stMin3rd impossible
  uninhabited LTMin1stMaj1st impossible
  uninhabited LTMin1stMaj2nd impossible
  uninhabited LTMin1stMaj3rd impossible
  uninhabited LTMin2ndMin3rd impossible
  uninhabited LTMin2ndMaj1st impossible
  uninhabited LTMin2ndMaj2nd impossible
  uninhabited LTMin2ndMaj3rd impossible
  uninhabited LTMin3rdMaj1st impossible
  uninhabited LTMin3rdMaj2nd impossible
  uninhabited LTMin3rdMaj3rd impossible
  uninhabited LTMaj1stMaj2nd impossible
  uninhabited LTMaj1stMaj3rd impossible
  uninhabited LTMaj2ndMaj3rd impossible
implementation Uninhabited (LTCharKind Maj2nd Min1st) where
  uninhabited LTSymNum impossible
  uninhabited LTSymMin1st impossible
  uninhabited LTSymMin2nd impossible
  uninhabited LTSymMin3rd impossible
  uninhabited LTSymMaj1st impossible
  uninhabited LTSymMaj2nd impossible
  uninhabited LTSymMaj3rd impossible
  uninhabited LTNumMin1st impossible
  uninhabited LTNumMin2nd impossible
  uninhabited LTNumMin3rd impossible
  uninhabited LTNumMaj1st impossible
  uninhabited LTNumMaj2nd impossible
  uninhabited LTNumMaj3rd impossible
  uninhabited LTMin1stMin2nd impossible
  uninhabited LTMin1stMin3rd impossible
  uninhabited LTMin1stMaj1st impossible
  uninhabited LTMin1stMaj2nd impossible
  uninhabited LTMin1stMaj3rd impossible
  uninhabited LTMin2ndMin3rd impossible
  uninhabited LTMin2ndMaj1st impossible
  uninhabited LTMin2ndMaj2nd impossible
  uninhabited LTMin2ndMaj3rd impossible
  uninhabited LTMin3rdMaj1st impossible
  uninhabited LTMin3rdMaj2nd impossible
  uninhabited LTMin3rdMaj3rd impossible
  uninhabited LTMaj1stMaj2nd impossible
  uninhabited LTMaj1stMaj3rd impossible
  uninhabited LTMaj2ndMaj3rd impossible
implementation Uninhabited (LTCharKind Maj2nd Min2nd) where
  uninhabited LTSymNum impossible
  uninhabited LTSymMin1st impossible
  uninhabited LTSymMin2nd impossible
  uninhabited LTSymMin3rd impossible
  uninhabited LTSymMaj1st impossible
  uninhabited LTSymMaj2nd impossible
  uninhabited LTSymMaj3rd impossible
  uninhabited LTNumMin1st impossible
  uninhabited LTNumMin2nd impossible
  uninhabited LTNumMin3rd impossible
  uninhabited LTNumMaj1st impossible
  uninhabited LTNumMaj2nd impossible
  uninhabited LTNumMaj3rd impossible
  uninhabited LTMin1stMin2nd impossible
  uninhabited LTMin1stMin3rd impossible
  uninhabited LTMin1stMaj1st impossible
  uninhabited LTMin1stMaj2nd impossible
  uninhabited LTMin1stMaj3rd impossible
  uninhabited LTMin2ndMin3rd impossible
  uninhabited LTMin2ndMaj1st impossible
  uninhabited LTMin2ndMaj2nd impossible
  uninhabited LTMin2ndMaj3rd impossible
  uninhabited LTMin3rdMaj1st impossible
  uninhabited LTMin3rdMaj2nd impossible
  uninhabited LTMin3rdMaj3rd impossible
  uninhabited LTMaj1stMaj2nd impossible
  uninhabited LTMaj1stMaj3rd impossible
  uninhabited LTMaj2ndMaj3rd impossible
implementation Uninhabited (LTCharKind Maj2nd Min3rd) where
  uninhabited LTSymNum impossible
  uninhabited LTSymMin1st impossible
  uninhabited LTSymMin2nd impossible
  uninhabited LTSymMin3rd impossible
  uninhabited LTSymMaj1st impossible
  uninhabited LTSymMaj2nd impossible
  uninhabited LTSymMaj3rd impossible
  uninhabited LTNumMin1st impossible
  uninhabited LTNumMin2nd impossible
  uninhabited LTNumMin3rd impossible
  uninhabited LTNumMaj1st impossible
  uninhabited LTNumMaj2nd impossible
  uninhabited LTNumMaj3rd impossible
  uninhabited LTMin1stMin2nd impossible
  uninhabited LTMin1stMin3rd impossible
  uninhabited LTMin1stMaj1st impossible
  uninhabited LTMin1stMaj2nd impossible
  uninhabited LTMin1stMaj3rd impossible
  uninhabited LTMin2ndMin3rd impossible
  uninhabited LTMin2ndMaj1st impossible
  uninhabited LTMin2ndMaj2nd impossible
  uninhabited LTMin2ndMaj3rd impossible
  uninhabited LTMin3rdMaj1st impossible
  uninhabited LTMin3rdMaj2nd impossible
  uninhabited LTMin3rdMaj3rd impossible
  uninhabited LTMaj1stMaj2nd impossible
  uninhabited LTMaj1stMaj3rd impossible
  uninhabited LTMaj2ndMaj3rd impossible
implementation Uninhabited (LTCharKind Maj2nd Maj1st) where
  uninhabited LTSymNum impossible
  uninhabited LTSymMin1st impossible
  uninhabited LTSymMin2nd impossible
  uninhabited LTSymMin3rd impossible
  uninhabited LTSymMaj1st impossible
  uninhabited LTSymMaj2nd impossible
  uninhabited LTSymMaj3rd impossible
  uninhabited LTNumMin1st impossible
  uninhabited LTNumMin2nd impossible
  uninhabited LTNumMin3rd impossible
  uninhabited LTNumMaj1st impossible
  uninhabited LTNumMaj2nd impossible
  uninhabited LTNumMaj3rd impossible
  uninhabited LTMin1stMin2nd impossible
  uninhabited LTMin1stMin3rd impossible
  uninhabited LTMin1stMaj1st impossible
  uninhabited LTMin1stMaj2nd impossible
  uninhabited LTMin1stMaj3rd impossible
  uninhabited LTMin2ndMin3rd impossible
  uninhabited LTMin2ndMaj1st impossible
  uninhabited LTMin2ndMaj2nd impossible
  uninhabited LTMin2ndMaj3rd impossible
  uninhabited LTMin3rdMaj1st impossible
  uninhabited LTMin3rdMaj2nd impossible
  uninhabited LTMin3rdMaj3rd impossible
  uninhabited LTMaj1stMaj2nd impossible
  uninhabited LTMaj1stMaj3rd impossible
  uninhabited LTMaj2ndMaj3rd impossible
implementation Uninhabited (LTCharKind Maj3rd y) where
  uninhabited LTSymNum impossible
  uninhabited LTSymMin1st impossible
  uninhabited LTSymMin2nd impossible
  uninhabited LTSymMin3rd impossible
  uninhabited LTSymMaj1st impossible
  uninhabited LTSymMaj2nd impossible
  uninhabited LTSymMaj3rd impossible
  uninhabited LTNumMin1st impossible
  uninhabited LTNumMin2nd impossible
  uninhabited LTNumMin3rd impossible
  uninhabited LTNumMaj1st impossible
  uninhabited LTNumMaj2nd impossible
  uninhabited LTNumMaj3rd impossible
  uninhabited LTMin1stMin2nd impossible
  uninhabited LTMin1stMin3rd impossible
  uninhabited LTMin1stMaj1st impossible
  uninhabited LTMin1stMaj2nd impossible
  uninhabited LTMin1stMaj3rd impossible
  uninhabited LTMin2ndMin3rd impossible
  uninhabited LTMin2ndMaj1st impossible
  uninhabited LTMin2ndMaj2nd impossible
  uninhabited LTMin2ndMaj3rd impossible
  uninhabited LTMin3rdMaj1st impossible
  uninhabited LTMin3rdMaj2nd impossible
  uninhabited LTMin3rdMaj3rd impossible
  uninhabited LTMaj1stMaj2nd impossible
  uninhabited LTMaj1stMaj3rd impossible
  uninhabited LTMaj2ndMaj3rd impossible


isLTCharKind : (x : CharKind) -> (y : CharKind) -> Dec (LTCharKind x y)
isLTCharKind Sym    Num    = Yes LTSymNum
isLTCharKind Sym    Min1st = Yes LTSymMin1st
isLTCharKind Sym    Min2nd = Yes LTSymMin2nd
isLTCharKind Sym    Min3rd = Yes LTSymMin3rd
isLTCharKind Sym    Maj1st = Yes LTSymMaj1st
isLTCharKind Sym    Maj2nd = Yes LTSymMaj2nd
isLTCharKind Sym    Maj3rd = Yes LTSymMaj3rd
isLTCharKind Num    Min1st = Yes LTNumMin1st
isLTCharKind Num    Min2nd = Yes LTNumMin2nd
isLTCharKind Num    Min3rd = Yes LTNumMin3rd
isLTCharKind Num    Maj1st = Yes LTNumMaj1st
isLTCharKind Num    Maj2nd = Yes LTNumMaj2nd
isLTCharKind Num    Maj3rd = Yes LTNumMaj3rd
isLTCharKind Min1st Min2nd = Yes LTMin1stMin2nd
isLTCharKind Min1st Min3rd = Yes LTMin1stMin3rd
isLTCharKind Min1st Maj1st = Yes LTMin1stMaj1st
isLTCharKind Min1st Maj2nd = Yes LTMin1stMaj2nd
isLTCharKind Min1st Maj3rd = Yes LTMin1stMaj3rd
isLTCharKind Min2nd Min3rd = Yes LTMin2ndMin3rd
isLTCharKind Min2nd Maj1st = Yes LTMin2ndMaj1st
isLTCharKind Min2nd Maj2nd = Yes LTMin2ndMaj2nd
isLTCharKind Min2nd Maj3rd = Yes LTMin2ndMaj3rd
isLTCharKind Min3rd Maj1st = Yes LTMin3rdMaj1st
isLTCharKind Min3rd Maj2nd = Yes LTMin3rdMaj2nd
isLTCharKind Min3rd Maj3rd = Yes LTMin3rdMaj3rd
isLTCharKind Maj1st Maj2nd = Yes LTMaj1stMaj2nd
isLTCharKind Maj1st Maj3rd = Yes LTMaj1stMaj3rd
isLTCharKind Maj2nd Maj3rd = Yes LTMaj2ndMaj3rd

isLTCharKind Sym    Sym    = No absurd
isLTCharKind Num    Sym    = No absurd
isLTCharKind Num    Num    = No absurd
isLTCharKind Min1st Sym    = No absurd
isLTCharKind Min1st Num    = No absurd
isLTCharKind Min1st Min1st = No absurd
isLTCharKind Min2nd Sym    = No absurd
isLTCharKind Min2nd Num    = No absurd
isLTCharKind Min2nd Min1st = No absurd
isLTCharKind Min2nd Min2nd = No absurd
isLTCharKind Min3rd Sym    = No absurd
isLTCharKind Min3rd Num    = No absurd
isLTCharKind Min3rd Min1st = No absurd
isLTCharKind Min3rd Min2nd = No absurd
isLTCharKind Min3rd Min3rd = No absurd
isLTCharKind Maj1st Sym    = No absurd
isLTCharKind Maj1st Num    = No absurd
isLTCharKind Maj1st Min1st = No absurd
isLTCharKind Maj1st Min2nd = No absurd
isLTCharKind Maj1st Min3rd = No absurd
isLTCharKind Maj1st Maj1st = No absurd
isLTCharKind Maj2nd Sym    = No absurd
isLTCharKind Maj2nd Num    = No absurd
isLTCharKind Maj2nd Min1st = No absurd
isLTCharKind Maj2nd Min2nd = No absurd
isLTCharKind Maj2nd Min3rd = No absurd
isLTCharKind Maj2nd Maj1st = No absurd
isLTCharKind Maj2nd Maj2nd = No absurd
isLTCharKind Maj3rd y      = No absurd

singLTCharKind : (x,y : CharKind) -> (p,q : LTCharKind x y) -> p = q
singLTCharKind Sym    Num    LTSymNum       LTSymNum       = Refl
singLTCharKind Sym    Min1st LTSymMin1st    LTSymMin1st    = Refl
singLTCharKind Sym    Min2nd LTSymMin2nd    LTSymMin2nd    = Refl
singLTCharKind Sym    Min3rd LTSymMin3rd    LTSymMin3rd    = Refl
singLTCharKind Sym    Maj1st LTSymMaj1st    LTSymMaj1st    = Refl
singLTCharKind Sym    Maj2nd LTSymMaj2nd    LTSymMaj2nd    = Refl
singLTCharKind Sym    Maj3rd LTSymMaj3rd    LTSymMaj3rd    = Refl
singLTCharKind Num    Min1st LTNumMin1st    LTNumMin1st    = Refl
singLTCharKind Num    Min2nd LTNumMin2nd    LTNumMin2nd    = Refl
singLTCharKind Num    Min3rd LTNumMin3rd    LTNumMin3rd    = Refl
singLTCharKind Num    Maj1st LTNumMaj1st    LTNumMaj1st    = Refl
singLTCharKind Num    Maj2nd LTNumMaj2nd    LTNumMaj2nd    = Refl
singLTCharKind Num    Maj3rd LTNumMaj3rd    LTNumMaj3rd    = Refl
singLTCharKind Min1st Min2nd LTMin1stMin2nd LTMin1stMin2nd = Refl
singLTCharKind Min1st Min3rd LTMin1stMin3rd LTMin1stMin3rd = Refl
singLTCharKind Min1st Maj1st LTMin1stMaj1st LTMin1stMaj1st = Refl
singLTCharKind Min1st Maj2nd LTMin1stMaj2nd LTMin1stMaj2nd = Refl
singLTCharKind Min1st Maj3rd LTMin1stMaj3rd LTMin1stMaj3rd = Refl
singLTCharKind Min2nd Min3rd LTMin2ndMin3rd LTMin2ndMin3rd = Refl
singLTCharKind Min2nd Maj1st LTMin2ndMaj1st LTMin2ndMaj1st = Refl
singLTCharKind Min2nd Maj2nd LTMin2ndMaj2nd LTMin2ndMaj2nd = Refl
singLTCharKind Min2nd Maj3rd LTMin2ndMaj3rd LTMin2ndMaj3rd = Refl
singLTCharKind Min3rd Maj1st LTMin3rdMaj1st LTMin3rdMaj1st = Refl
singLTCharKind Min3rd Maj2nd LTMin3rdMaj2nd LTMin3rdMaj2nd = Refl
singLTCharKind Min3rd Maj3rd LTMin3rdMaj3rd LTMin3rdMaj3rd = Refl
singLTCharKind Maj1st Maj2nd LTMaj1stMaj2nd LTMaj1stMaj2nd = Refl
singLTCharKind Maj1st Maj3rd LTMaj1stMaj3rd LTMaj1stMaj3rd = Refl
singLTCharKind Maj2nd Maj3rd LTMaj2ndMaj3rd LTMaj2ndMaj3rd = Refl

irreflLTCharKind : (x : CharKind) -> (p : LTCharKind x x) -> Void
irreflLTCharKind x = absurd

antisymLTCharKind : (x,y : CharKind) -> (p : LTCharKind x y) -> (q : LTCharKind y x) -> Void
antisymLTCharKind Sym    Num    LTSymNum       = absurd
antisymLTCharKind Sym    Min1st LTSymMin1st    = absurd
antisymLTCharKind Sym    Min2nd LTSymMin2nd    = absurd
antisymLTCharKind Sym    Min3rd LTSymMin3rd    = absurd
antisymLTCharKind Sym    Maj1st LTSymMaj1st    = absurd
antisymLTCharKind Sym    Maj2nd LTSymMaj2nd    = absurd
antisymLTCharKind Sym    Maj3rd LTSymMaj3rd    = absurd
antisymLTCharKind Num    Min1st LTNumMin1st    = absurd
antisymLTCharKind Num    Min2nd LTNumMin2nd    = absurd
antisymLTCharKind Num    Min3rd LTNumMin3rd    = absurd
antisymLTCharKind Num    Maj1st LTNumMaj1st    = absurd
antisymLTCharKind Num    Maj2nd LTNumMaj2nd    = absurd
antisymLTCharKind Num    Maj3rd LTNumMaj3rd    = absurd
antisymLTCharKind Min1st Min2nd LTMin1stMin2nd = absurd
antisymLTCharKind Min1st Min3rd LTMin1stMin3rd = absurd
antisymLTCharKind Min1st Maj1st LTMin1stMaj1st = absurd
antisymLTCharKind Min1st Maj2nd LTMin1stMaj2nd = absurd
antisymLTCharKind Min1st Maj3rd LTMin1stMaj3rd = absurd
antisymLTCharKind Min2nd Min3rd LTMin2ndMin3rd = absurd
antisymLTCharKind Min2nd Maj1st LTMin2ndMaj1st = absurd
antisymLTCharKind Min2nd Maj2nd LTMin2ndMaj2nd = absurd
antisymLTCharKind Min2nd Maj3rd LTMin2ndMaj3rd = absurd
antisymLTCharKind Min3rd Maj1st LTMin3rdMaj1st = absurd
antisymLTCharKind Min3rd Maj2nd LTMin3rdMaj2nd = absurd
antisymLTCharKind Min3rd Maj3rd LTMin3rdMaj3rd = absurd
antisymLTCharKind Maj1st Maj2nd LTMaj1stMaj2nd = absurd
antisymLTCharKind Maj1st Maj3rd LTMaj1stMaj3rd = absurd
antisymLTCharKind Maj2nd Maj3rd LTMaj2ndMaj3rd = absurd

transLTCharKind : (x,y,z : CharKind)
               -> (p : LTCharKind x y)
               -> (q : LTCharKind y z)
               -> LTCharKind x z
transLTCharKind Sym Num Min1st LTSymNum LTNumMin1st = LTSymMin1st
transLTCharKind Sym Num Min2nd LTSymNum LTNumMin2nd = LTSymMin2nd
transLTCharKind Sym Num Min3rd LTSymNum LTNumMin3rd = LTSymMin3rd
transLTCharKind Sym Num Maj1st LTSymNum LTNumMaj1st = LTSymMaj1st
transLTCharKind Sym Num Maj2nd LTSymNum LTNumMaj2nd = LTSymMaj2nd
transLTCharKind Sym Num Maj3rd LTSymNum LTNumMaj3rd = LTSymMaj3rd
transLTCharKind Sym Min1st Min2nd LTSymMin1st LTMin1stMin2nd = LTSymMin2nd
transLTCharKind Sym Min1st Min3rd LTSymMin1st LTMin1stMin3rd = LTSymMin3rd
transLTCharKind Sym Min1st Maj1st LTSymMin1st LTMin1stMaj1st = LTSymMaj1st
transLTCharKind Sym Min1st Maj2nd LTSymMin1st LTMin1stMaj2nd = LTSymMaj2nd
transLTCharKind Sym Min1st Maj3rd LTSymMin1st LTMin1stMaj3rd = LTSymMaj3rd
transLTCharKind Sym Min2nd Min3rd LTSymMin2nd LTMin2ndMin3rd = LTSymMin3rd
transLTCharKind Sym Min2nd Maj1st LTSymMin2nd LTMin2ndMaj1st = LTSymMaj1st
transLTCharKind Sym Min2nd Maj2nd LTSymMin2nd LTMin2ndMaj2nd = LTSymMaj2nd
transLTCharKind Sym Min2nd Maj3rd LTSymMin2nd LTMin2ndMaj3rd = LTSymMaj3rd
transLTCharKind Sym Min3rd Maj1st LTSymMin3rd LTMin3rdMaj1st = LTSymMaj1st
transLTCharKind Sym Min3rd Maj2nd LTSymMin3rd LTMin3rdMaj2nd = LTSymMaj2nd
transLTCharKind Sym Min3rd Maj3rd LTSymMin3rd LTMin3rdMaj3rd = LTSymMaj3rd
transLTCharKind Sym Maj1st Maj2nd LTSymMaj1st LTMaj1stMaj2nd = LTSymMaj2nd
transLTCharKind Sym Maj1st Maj3rd LTSymMaj1st LTMaj1stMaj3rd = LTSymMaj3rd
transLTCharKind Sym Maj2nd Maj3rd LTSymMaj2nd LTMaj2ndMaj3rd = LTSymMaj3rd
transLTCharKind Num Min1st Min2nd LTNumMin1st LTMin1stMin2nd = LTNumMin2nd
transLTCharKind Num Min1st Min3rd LTNumMin1st LTMin1stMin3rd = LTNumMin3rd
transLTCharKind Num Min1st Maj1st LTNumMin1st LTMin1stMaj1st = LTNumMaj1st
transLTCharKind Num Min1st Maj2nd LTNumMin1st LTMin1stMaj2nd = LTNumMaj2nd
transLTCharKind Num Min1st Maj3rd LTNumMin1st LTMin1stMaj3rd = LTNumMaj3rd
transLTCharKind Num Min2nd Min3rd LTNumMin2nd LTMin2ndMin3rd = LTNumMin3rd
transLTCharKind Num Min2nd Maj1st LTNumMin2nd LTMin2ndMaj1st = LTNumMaj1st
transLTCharKind Num Min2nd Maj2nd LTNumMin2nd LTMin2ndMaj2nd = LTNumMaj2nd
transLTCharKind Num Min2nd Maj3rd LTNumMin2nd LTMin2ndMaj3rd = LTNumMaj3rd
transLTCharKind Num Min3rd Maj1st LTNumMin3rd LTMin3rdMaj1st = LTNumMaj1st
transLTCharKind Num Min3rd Maj2nd LTNumMin3rd LTMin3rdMaj2nd = LTNumMaj2nd
transLTCharKind Num Min3rd Maj3rd LTNumMin3rd LTMin3rdMaj3rd = LTNumMaj3rd
transLTCharKind Num Maj1st Maj2nd LTNumMaj1st LTMaj1stMaj2nd = LTNumMaj2nd
transLTCharKind Num Maj1st Maj3rd LTNumMaj1st LTMaj1stMaj3rd = LTNumMaj3rd
transLTCharKind Num Maj2nd Maj3rd LTNumMaj2nd LTMaj2ndMaj3rd = LTNumMaj3rd
transLTCharKind Min1st Min2nd Min3rd LTMin1stMin2nd LTMin2ndMin3rd = LTMin1stMin3rd
transLTCharKind Min1st Min2nd Maj1st LTMin1stMin2nd LTMin2ndMaj1st = LTMin1stMaj1st
transLTCharKind Min1st Min2nd Maj2nd LTMin1stMin2nd LTMin2ndMaj2nd = LTMin1stMaj2nd
transLTCharKind Min1st Min2nd Maj3rd LTMin1stMin2nd LTMin2ndMaj3rd = LTMin1stMaj3rd
transLTCharKind Min1st Min3rd Maj1st LTMin1stMin3rd LTMin3rdMaj1st = LTMin1stMaj1st
transLTCharKind Min1st Min3rd Maj2nd LTMin1stMin3rd LTMin3rdMaj2nd = LTMin1stMaj2nd
transLTCharKind Min1st Min3rd Maj3rd LTMin1stMin3rd LTMin3rdMaj3rd = LTMin1stMaj3rd
transLTCharKind Min1st Maj1st Maj2nd LTMin1stMaj1st LTMaj1stMaj2nd = LTMin1stMaj2nd
transLTCharKind Min1st Maj1st Maj3rd LTMin1stMaj1st LTMaj1stMaj3rd = LTMin1stMaj3rd
transLTCharKind Min1st Maj2nd Maj3rd LTMin1stMaj2nd LTMaj2ndMaj3rd = LTMin1stMaj3rd
transLTCharKind Min2nd Min3rd Maj1st LTMin2ndMin3rd LTMin3rdMaj1st = LTMin2ndMaj1st
transLTCharKind Min2nd Min3rd Maj2nd LTMin2ndMin3rd LTMin3rdMaj2nd = LTMin2ndMaj2nd
transLTCharKind Min2nd Min3rd Maj3rd LTMin2ndMin3rd LTMin3rdMaj3rd = LTMin2ndMaj3rd
transLTCharKind Min2nd Maj1st Maj2nd LTMin2ndMaj1st LTMaj1stMaj2nd = LTMin2ndMaj2nd
transLTCharKind Min2nd Maj1st Maj3rd LTMin2ndMaj1st LTMaj1stMaj3rd = LTMin2ndMaj3rd
transLTCharKind Min2nd Maj2nd Maj3rd LTMin2ndMaj2nd LTMaj2ndMaj3rd = LTMin2ndMaj3rd
transLTCharKind Min3rd Maj1st Maj2nd LTMin3rdMaj1st LTMaj1stMaj2nd = LTMin3rdMaj2nd
transLTCharKind Min3rd Maj1st Maj3rd LTMin3rdMaj1st LTMaj1stMaj3rd = LTMin3rdMaj3rd
transLTCharKind Min3rd Maj2nd Maj3rd LTMin3rdMaj2nd LTMaj2ndMaj3rd = LTMin3rdMaj3rd
transLTCharKind Maj1st Maj2nd Maj3rd LTMaj1stMaj2nd LTMaj2ndMaj3rd = LTMaj1stMaj3rd
transLTCharKind Maj2nd Maj3rd z LTMaj2ndMaj3rd _ impossible

---------------------------------------------------------------------------------------------------
-- [DecEq] ----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

implementation Uninhabited (Sym    = Num)    where
  uninhabited Refl impossible 
implementation Uninhabited (Sym    = Min1st) where
  uninhabited Refl impossible 
implementation Uninhabited (Sym    = Min2nd) where
  uninhabited Refl impossible 
implementation Uninhabited (Sym    = Min3rd) where
  uninhabited Refl impossible 
implementation Uninhabited (Sym    = Maj1st) where
  uninhabited Refl impossible 
implementation Uninhabited (Sym    = Maj2nd) where
  uninhabited Refl impossible 
implementation Uninhabited (Sym    = Maj3rd) where
  uninhabited Refl impossible 
implementation Uninhabited (Num    = Min1st) where
  uninhabited Refl impossible 
implementation Uninhabited (Num    = Min2nd) where
  uninhabited Refl impossible 
implementation Uninhabited (Num    = Min3rd) where
  uninhabited Refl impossible 
implementation Uninhabited (Num    = Maj1st) where
  uninhabited Refl impossible 
implementation Uninhabited (Num    = Maj2nd) where
  uninhabited Refl impossible 
implementation Uninhabited (Num    = Maj3rd) where
  uninhabited Refl impossible 
implementation Uninhabited (Min1st = Min2nd) where
  uninhabited Refl impossible 
implementation Uninhabited (Min1st = Min3rd) where
  uninhabited Refl impossible 
implementation Uninhabited (Min1st = Maj1st) where
  uninhabited Refl impossible 
implementation Uninhabited (Min1st = Maj2nd) where
  uninhabited Refl impossible 
implementation Uninhabited (Min1st = Maj3rd) where
  uninhabited Refl impossible 
implementation Uninhabited (Min2nd = Min3rd) where
  uninhabited Refl impossible 
implementation Uninhabited (Min2nd = Maj1st) where
  uninhabited Refl impossible 
implementation Uninhabited (Min2nd = Maj2nd) where
  uninhabited Refl impossible 
implementation Uninhabited (Min2nd = Maj3rd) where
  uninhabited Refl impossible 
implementation Uninhabited (Min3rd = Maj1st) where
  uninhabited Refl impossible 
implementation Uninhabited (Min3rd = Maj2nd) where
  uninhabited Refl impossible 
implementation Uninhabited (Min3rd = Maj3rd) where
  uninhabited Refl impossible 
implementation Uninhabited (Maj1st = Maj2nd) where
  uninhabited Refl impossible 
implementation Uninhabited (Maj1st = Maj3rd) where
  uninhabited Refl impossible 
implementation Uninhabited (Maj2nd = Maj3rd) where
  uninhabited Refl impossible 

decEqCharKind : (x,y : CharKind) -> Dec (x = y)
decEqCharKind Sym    Sym    = Yes Refl
decEqCharKind Num    Num    = Yes Refl
decEqCharKind Min1st Min1st = Yes Refl
decEqCharKind Min2nd Min2nd = Yes Refl
decEqCharKind Min3rd Min3rd = Yes Refl
decEqCharKind Maj1st Maj1st = Yes Refl
decEqCharKind Maj2nd Maj2nd = Yes Refl
decEqCharKind Maj3rd Maj3rd = Yes Refl

decEqCharKind Sym    Num    = No absurd
decEqCharKind Sym    Min1st = No absurd
decEqCharKind Sym    Min2nd = No absurd
decEqCharKind Sym    Min3rd = No absurd
decEqCharKind Sym    Maj1st = No absurd
decEqCharKind Sym    Maj2nd = No absurd
decEqCharKind Sym    Maj3rd = No absurd
decEqCharKind Num    Min1st = No absurd
decEqCharKind Num    Min2nd = No absurd
decEqCharKind Num    Min3rd = No absurd
decEqCharKind Num    Maj1st = No absurd
decEqCharKind Num    Maj2nd = No absurd
decEqCharKind Num    Maj3rd = No absurd
decEqCharKind Min1st Min2nd = No absurd
decEqCharKind Min1st Min3rd = No absurd
decEqCharKind Min1st Maj1st = No absurd
decEqCharKind Min1st Maj2nd = No absurd
decEqCharKind Min1st Maj3rd = No absurd
decEqCharKind Min2nd Min3rd = No absurd
decEqCharKind Min2nd Maj1st = No absurd
decEqCharKind Min2nd Maj2nd = No absurd
decEqCharKind Min2nd Maj3rd = No absurd
decEqCharKind Min3rd Maj1st = No absurd
decEqCharKind Min3rd Maj2nd = No absurd
decEqCharKind Min3rd Maj3rd = No absurd
decEqCharKind Maj1st Maj2nd = No absurd
decEqCharKind Maj1st Maj3rd = No absurd
decEqCharKind Maj2nd Maj3rd = No absurd
decEqCharKind  Num    Sym    = No (absurd . sym)
decEqCharKind  Min1st Sym    = No (absurd . sym)
decEqCharKind  Min2nd Sym    = No (absurd . sym)
decEqCharKind  Min3rd Sym    = No (absurd . sym)
decEqCharKind  Maj1st Sym    = No (absurd . sym)
decEqCharKind  Maj2nd Sym    = No (absurd . sym)
decEqCharKind  Maj3rd Sym    = No (absurd . sym)
decEqCharKind  Min1st Num    = No (absurd . sym)
decEqCharKind  Min2nd Num    = No (absurd . sym)
decEqCharKind  Min3rd Num    = No (absurd . sym)
decEqCharKind  Maj1st Num    = No (absurd . sym)
decEqCharKind  Maj2nd Num    = No (absurd . sym)
decEqCharKind  Maj3rd Num    = No (absurd . sym)
decEqCharKind  Min2nd Min1st = No (absurd . sym)
decEqCharKind  Min3rd Min1st = No (absurd . sym)
decEqCharKind  Maj1st Min1st = No (absurd . sym)
decEqCharKind  Maj2nd Min1st = No (absurd . sym)
decEqCharKind  Maj3rd Min1st = No (absurd . sym)
decEqCharKind  Min3rd Min2nd = No (absurd . sym)
decEqCharKind  Maj1st Min2nd = No (absurd . sym)
decEqCharKind  Maj2nd Min2nd = No (absurd . sym)
decEqCharKind  Maj3rd Min2nd = No (absurd . sym)
decEqCharKind  Maj1st Min3rd = No (absurd . sym)
decEqCharKind  Maj2nd Min3rd = No (absurd . sym)
decEqCharKind  Maj3rd Min3rd = No (absurd . sym)
decEqCharKind  Maj2nd Maj1st = No (absurd . sym)
decEqCharKind  Maj3rd Maj1st = No (absurd . sym)
decEqCharKind  Maj3rd Maj2nd = No (absurd . sym)

implementation DecEq CharKind where
  decEq = decEqCharKind

---------------------------------------------------------------------------------------------------
-- [Setoid] ---------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

SetoidCharKind : SetoidT CharKind
SetoidCharKind = (PropEqSetoid CharKind decEqCharKind)

---------------------------------------------------------------------------------------------------
-- [Trichotomy] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

{-
  Note for future self: simplify Trichotomy by indexing it via antisymmetry.
-}

trichoLTCharKind : (x,y : CharKind) -> Trichotomy SetoidCharKind LTCharKind x y
trichoLTCharKind Sym    Sym    = IsEq (\p => antisymLTCharKind Sym Sym p p)
trichoLTCharKind Num    Num    = IsEq (\p => antisymLTCharKind Num Num p p)
trichoLTCharKind Min1st Min1st = IsEq (\p => antisymLTCharKind Min1st Min1st p p)
trichoLTCharKind Min2nd Min2nd = IsEq (\p => antisymLTCharKind Min2nd Min2nd p p)
trichoLTCharKind Min3rd Min3rd = IsEq (\p => antisymLTCharKind Min3rd Min3rd p p)
trichoLTCharKind Maj1st Maj1st = IsEq (\p => antisymLTCharKind Maj1st Maj1st p p)
trichoLTCharKind Maj2nd Maj2nd = IsEq (\p => antisymLTCharKind Maj2nd Maj2nd p p)
trichoLTCharKind Maj3rd Maj3rd = IsEq (\p => antisymLTCharKind Maj3rd Maj3rd p p)

trichoLTCharKind Sym    Num    =
  IsBinR_xRy LTSymNum (antisymLTCharKind Sym Num LTSymNum) absurd
trichoLTCharKind Sym    Min1st =
  IsBinR_xRy LTSymMin1st (antisymLTCharKind Sym Min1st LTSymMin1st) absurd
trichoLTCharKind Sym    Min2nd =
  IsBinR_xRy LTSymMin2nd (antisymLTCharKind Sym Min2nd LTSymMin2nd) absurd
trichoLTCharKind Sym    Min3rd =
  IsBinR_xRy LTSymMin3rd (antisymLTCharKind Sym Min3rd LTSymMin3rd) absurd
trichoLTCharKind Sym    Maj1st =
  IsBinR_xRy LTSymMaj1st (antisymLTCharKind Sym Maj1st LTSymMaj1st) absurd
trichoLTCharKind Sym    Maj2nd =
  IsBinR_xRy LTSymMaj2nd (antisymLTCharKind Sym Maj2nd LTSymMaj2nd) absurd
trichoLTCharKind Sym    Maj3rd =
  IsBinR_xRy LTSymMaj3rd (antisymLTCharKind Sym Maj3rd LTSymMaj3rd) absurd
trichoLTCharKind Num    Min1st =
  IsBinR_xRy LTNumMin1st (antisymLTCharKind Num Min1st LTNumMin1st) absurd
trichoLTCharKind Num    Min2nd =
  IsBinR_xRy LTNumMin2nd (antisymLTCharKind Num Min2nd LTNumMin2nd) absurd
trichoLTCharKind Num    Min3rd =
  IsBinR_xRy LTNumMin3rd (antisymLTCharKind Num Min3rd LTNumMin3rd) absurd
trichoLTCharKind Num    Maj1st =
  IsBinR_xRy LTNumMaj1st (antisymLTCharKind Num Maj1st LTNumMaj1st) absurd
trichoLTCharKind Num    Maj2nd =
  IsBinR_xRy LTNumMaj2nd (antisymLTCharKind Num Maj2nd LTNumMaj2nd) absurd
trichoLTCharKind Num    Maj3rd =
  IsBinR_xRy LTNumMaj3rd (antisymLTCharKind Num Maj3rd LTNumMaj3rd) absurd
trichoLTCharKind Min1st Min2nd =
  IsBinR_xRy LTMin1stMin2nd (antisymLTCharKind Min1st Min2nd LTMin1stMin2nd) absurd
trichoLTCharKind Min1st Min3rd =
  IsBinR_xRy LTMin1stMin3rd (antisymLTCharKind Min1st Min3rd LTMin1stMin3rd) absurd
trichoLTCharKind Min1st Maj1st =
  IsBinR_xRy LTMin1stMaj1st (antisymLTCharKind Min1st Maj1st LTMin1stMaj1st) absurd
trichoLTCharKind Min1st Maj2nd =
  IsBinR_xRy LTMin1stMaj2nd (antisymLTCharKind Min1st Maj2nd LTMin1stMaj2nd) absurd
trichoLTCharKind Min1st Maj3rd =
  IsBinR_xRy LTMin1stMaj3rd (antisymLTCharKind Min1st Maj3rd LTMin1stMaj3rd) absurd
trichoLTCharKind Min2nd Min3rd =
  IsBinR_xRy LTMin2ndMin3rd (antisymLTCharKind Min2nd Min3rd LTMin2ndMin3rd) absurd
trichoLTCharKind Min2nd Maj1st =
  IsBinR_xRy LTMin2ndMaj1st (antisymLTCharKind Min2nd Maj1st LTMin2ndMaj1st) absurd
trichoLTCharKind Min2nd Maj2nd =
  IsBinR_xRy LTMin2ndMaj2nd (antisymLTCharKind Min2nd Maj2nd LTMin2ndMaj2nd) absurd
trichoLTCharKind Min2nd Maj3rd =
  IsBinR_xRy LTMin2ndMaj3rd (antisymLTCharKind Min2nd Maj3rd LTMin2ndMaj3rd) absurd
trichoLTCharKind Min3rd Maj1st =
  IsBinR_xRy LTMin3rdMaj1st (antisymLTCharKind Min3rd Maj1st LTMin3rdMaj1st) absurd
trichoLTCharKind Min3rd Maj2nd =
  IsBinR_xRy LTMin3rdMaj2nd (antisymLTCharKind Min3rd Maj2nd LTMin3rdMaj2nd) absurd
trichoLTCharKind Min3rd Maj3rd =
  IsBinR_xRy LTMin3rdMaj3rd (antisymLTCharKind Min3rd Maj3rd LTMin3rdMaj3rd) absurd
trichoLTCharKind Maj1st Maj2nd =
  IsBinR_xRy LTMaj1stMaj2nd (antisymLTCharKind Maj1st Maj2nd LTMaj1stMaj2nd) absurd
trichoLTCharKind Maj1st Maj3rd =
  IsBinR_xRy LTMaj1stMaj3rd (antisymLTCharKind Maj1st Maj3rd LTMaj1stMaj3rd) absurd
trichoLTCharKind Maj2nd Maj3rd =
  IsBinR_xRy LTMaj2ndMaj3rd (antisymLTCharKind Maj2nd Maj3rd LTMaj2ndMaj3rd) absurd
trichoLTCharKind  Num    Sym    =
  IsBinR_yRx LTSymNum (antisymLTCharKind Sym Num LTSymNum) (absurd . sym)
trichoLTCharKind  Min1st Sym    =
  IsBinR_yRx LTSymMin1st (antisymLTCharKind Sym Min1st LTSymMin1st) (absurd . sym)
trichoLTCharKind  Min2nd Sym    =
  IsBinR_yRx LTSymMin2nd (antisymLTCharKind Sym Min2nd LTSymMin2nd) (absurd . sym)
trichoLTCharKind  Min3rd Sym    =
  IsBinR_yRx LTSymMin3rd (antisymLTCharKind Sym Min3rd LTSymMin3rd) (absurd . sym)
trichoLTCharKind  Maj1st Sym    =
  IsBinR_yRx LTSymMaj1st (antisymLTCharKind Sym Maj1st LTSymMaj1st) (absurd . sym)
trichoLTCharKind  Maj2nd Sym    =
  IsBinR_yRx LTSymMaj2nd (antisymLTCharKind Sym Maj2nd LTSymMaj2nd) (absurd . sym)
trichoLTCharKind  Maj3rd Sym    =
  IsBinR_yRx LTSymMaj3rd (antisymLTCharKind Sym Maj3rd LTSymMaj3rd) (absurd . sym)
trichoLTCharKind  Min1st Num    =
  IsBinR_yRx LTNumMin1st (antisymLTCharKind Num Min1st LTNumMin1st) (absurd . sym)
trichoLTCharKind  Min2nd Num    =
  IsBinR_yRx LTNumMin2nd (antisymLTCharKind Num Min2nd LTNumMin2nd) (absurd . sym)
trichoLTCharKind  Min3rd Num    =
  IsBinR_yRx LTNumMin3rd (antisymLTCharKind Num Min3rd LTNumMin3rd) (absurd . sym)
trichoLTCharKind  Maj1st Num    =
  IsBinR_yRx LTNumMaj1st (antisymLTCharKind Num Maj1st LTNumMaj1st) (absurd . sym)
trichoLTCharKind  Maj2nd Num    =
  IsBinR_yRx LTNumMaj2nd (antisymLTCharKind Num Maj2nd LTNumMaj2nd) (absurd . sym)
trichoLTCharKind  Maj3rd Num    =
  IsBinR_yRx LTNumMaj3rd (antisymLTCharKind Num Maj3rd LTNumMaj3rd) (absurd . sym)
trichoLTCharKind  Min2nd Min1st =
  IsBinR_yRx LTMin1stMin2nd (antisymLTCharKind Min1st Min2nd LTMin1stMin2nd) (absurd . sym)
trichoLTCharKind  Min3rd Min1st =
  IsBinR_yRx LTMin1stMin3rd (antisymLTCharKind Min1st Min3rd LTMin1stMin3rd) (absurd . sym)
trichoLTCharKind  Maj1st Min1st =
  IsBinR_yRx LTMin1stMaj1st (antisymLTCharKind Min1st Maj1st LTMin1stMaj1st) (absurd . sym)
trichoLTCharKind  Maj2nd Min1st =
  IsBinR_yRx LTMin1stMaj2nd (antisymLTCharKind Min1st Maj2nd LTMin1stMaj2nd) (absurd . sym)
trichoLTCharKind  Maj3rd Min1st =
  IsBinR_yRx LTMin1stMaj3rd (antisymLTCharKind Min1st Maj3rd LTMin1stMaj3rd) (absurd . sym)
trichoLTCharKind  Min3rd Min2nd =
  IsBinR_yRx LTMin2ndMin3rd (antisymLTCharKind Min2nd Min3rd LTMin2ndMin3rd) (absurd . sym)
trichoLTCharKind  Maj1st Min2nd =
  IsBinR_yRx LTMin2ndMaj1st (antisymLTCharKind Min2nd Maj1st LTMin2ndMaj1st) (absurd . sym)
trichoLTCharKind  Maj2nd Min2nd =
  IsBinR_yRx LTMin2ndMaj2nd (antisymLTCharKind Min2nd Maj2nd LTMin2ndMaj2nd) (absurd . sym)
trichoLTCharKind  Maj3rd Min2nd =
  IsBinR_yRx LTMin2ndMaj3rd (antisymLTCharKind Min2nd Maj3rd LTMin2ndMaj3rd) (absurd . sym)
trichoLTCharKind  Maj1st Min3rd =
  IsBinR_yRx LTMin3rdMaj1st (antisymLTCharKind Min3rd Maj1st LTMin3rdMaj1st) (absurd . sym)
trichoLTCharKind  Maj2nd Min3rd =
  IsBinR_yRx LTMin3rdMaj2nd (antisymLTCharKind Min3rd Maj2nd LTMin3rdMaj2nd) (absurd . sym)
trichoLTCharKind  Maj3rd Min3rd =
  IsBinR_yRx LTMin3rdMaj3rd (antisymLTCharKind Min3rd Maj3rd LTMin3rdMaj3rd) (absurd . sym)
trichoLTCharKind  Maj2nd Maj1st =
  IsBinR_yRx LTMaj1stMaj2nd (antisymLTCharKind Maj1st Maj2nd LTMaj1stMaj2nd) (absurd . sym)
trichoLTCharKind  Maj3rd Maj1st =
  IsBinR_yRx LTMaj1stMaj3rd (antisymLTCharKind Maj1st Maj3rd LTMaj1stMaj3rd) (absurd . sym)
trichoLTCharKind  Maj3rd Maj2nd =
  IsBinR_yRx LTMaj2ndMaj3rd (antisymLTCharKind Maj2nd Maj3rd LTMaj2ndMaj3rd) (absurd . sym)

TotalOrderingTCharKind : StrictTotalOrderingT CharKind SetoidCharKind
TotalOrderingTCharKind =
  MkSTOrderingT LTCharKind antisymLTCharKind transLTCharKind trichoLTCharKind isLTCharKind

TotalOrderingCharKind : StrictTotalOrdering CharKind
TotalOrderingCharKind =
  MkSTOrdering decEqCharKind (MkSTOrderingS TotalOrderingTCharKind singLTCharKind)