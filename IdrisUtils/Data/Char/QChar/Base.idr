module IdrisUtils.Data.Char.QChar.Base

import public IdrisUtils.Data.Char.CharKind

%default total

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| Idris uses ASCII and that makes the natural numbers too large if you just `toNat` them.
|||
||| Let's try to be a bit more clever...
|||
||| The alternative is defining LT over Char pairwise which is going to be painful...
public export
data QChar : Char -> (CharKind, Nat) -> Type where
  C_ : QChar '_' (Sym, 0)
  C' : QChar '\'' (Sym, 1)
  Cstop : QChar '.' (Sym, 2)

  C0 : QChar '0' (Num, 0)
  C1 : QChar '1' (Num, 1)
  C2 : QChar '2' (Num, 2)
  C3 : QChar '3' (Num, 3)
  C4 : QChar '4' (Num, 4)
  C5 : QChar '5' (Num, 5)
  C6 : QChar '6' (Num, 6)
  C7 : QChar '7' (Num, 7)
  C8 : QChar '8' (Num, 8)
  C9 : QChar '9' (Num, 9)

  Ca : QChar 'a' (Min1st, 0)
  Cb : QChar 'b' (Min1st, 1)
  Cc : QChar 'c' (Min1st, 2)
  Cd : QChar 'd' (Min1st, 3)
  Ce : QChar 'e' (Min1st, 4)
  Cf : QChar 'f' (Min1st, 5)
  Cg : QChar 'g' (Min1st, 6)
  Ch : QChar 'h' (Min1st, 7)
  Ci : QChar 'i' (Min1st, 8)
  Cj : QChar 'j' (Min1st, 9)
  Ck : QChar 'k' (Min2nd, 0)
  Cl : QChar 'l' (Min2nd, 1)
  Cm : QChar 'm' (Min2nd, 2)
  Cn : QChar 'n' (Min2nd, 3)
  Co : QChar 'o' (Min2nd, 4)
  Cp : QChar 'p' (Min2nd, 5)
  Cq : QChar 'q' (Min2nd, 6)
  Cr : QChar 'r' (Min2nd, 7)
  Cs : QChar 's' (Min2nd, 8)
  Ct : QChar 't' (Min2nd, 9)
  Cu : QChar 'u' (Min3rd, 0)
  Cv : QChar 'v' (Min3rd, 1)
  Cw : QChar 'w' (Min3rd, 2)
  Cx : QChar 'x' (Min3rd, 3)
  Cy : QChar 'y' (Min3rd, 4)
  Cz : QChar 'z' (Min3rd, 5)

  CA : QChar 'A' (Maj1st, 0)
  CB : QChar 'B' (Maj1st, 1)
  CC : QChar 'C' (Maj1st, 2)
  CD : QChar 'D' (Maj1st, 3)
  CE : QChar 'E' (Maj1st, 4)
  CF : QChar 'F' (Maj1st, 5)
  CG : QChar 'G' (Maj1st, 6)
  CH : QChar 'H' (Maj1st, 7)
  CI : QChar 'I' (Maj1st, 8)
  CJ : QChar 'J' (Maj1st, 9)
  CK : QChar 'K' (Maj2nd, 0)
  CL : QChar 'L' (Maj2nd, 1)
  CM : QChar 'M' (Maj2nd, 2)
  CN : QChar 'N' (Maj2nd, 3)
  CO : QChar 'O' (Maj2nd, 4)
  CP : QChar 'P' (Maj2nd, 5)
  CQ : QChar 'Q' (Maj2nd, 6)
  CR : QChar 'R' (Maj2nd, 7)
  CS : QChar 'S' (Maj2nd, 8)
  CT : QChar 'T' (Maj2nd, 9)
  CU : QChar 'U' (Maj3rd, 0)
  CV : QChar 'V' (Maj3rd, 1)
  CW : QChar 'W' (Maj3rd, 2)
  CX : QChar 'X' (Maj3rd, 3)
  CY : QChar 'Y' (Maj3rd, 4)
  CZ : QChar 'Z' (Maj3rd, 5)

---------------------------------------------------------------------------------------------------
-- [DecEq] ----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
decEqQChar0 : (x, y : QChar v i) -> Dec (x = y)
decEqQChar0 C_ C_ = Yes Refl
decEqQChar0 C' C' = Yes Refl
decEqQChar0 Cstop Cstop = Yes Refl
decEqQChar0 C0 C0 = Yes Refl
decEqQChar0 C1 C1 = Yes Refl
decEqQChar0 C2 C2 = Yes Refl
decEqQChar0 C3 C3 = Yes Refl
decEqQChar0 C4 C4 = Yes Refl
decEqQChar0 C5 C5 = Yes Refl
decEqQChar0 C6 C6 = Yes Refl
decEqQChar0 C7 C7 = Yes Refl
decEqQChar0 C8 C8 = Yes Refl
decEqQChar0 C9 C9 = Yes Refl
decEqQChar0 Ca Ca = Yes Refl
decEqQChar0 Cb Cb = Yes Refl
decEqQChar0 Cc Cc = Yes Refl
decEqQChar0 Cd Cd = Yes Refl
decEqQChar0 Ce Ce = Yes Refl
decEqQChar0 Cf Cf = Yes Refl
decEqQChar0 Cg Cg = Yes Refl
decEqQChar0 Ch Ch = Yes Refl
decEqQChar0 Ci Ci = Yes Refl
decEqQChar0 Cj Cj = Yes Refl
decEqQChar0 Ck Ck = Yes Refl
decEqQChar0 Cl Cl = Yes Refl
decEqQChar0 Cm Cm = Yes Refl
decEqQChar0 Cn Cn = Yes Refl
decEqQChar0 Co Co = Yes Refl
decEqQChar0 Cp Cp = Yes Refl
decEqQChar0 Cq Cq = Yes Refl
decEqQChar0 Cr Cr = Yes Refl
decEqQChar0 Cs Cs = Yes Refl
decEqQChar0 Ct Ct = Yes Refl
decEqQChar0 Cu Cu = Yes Refl
decEqQChar0 Cv Cv = Yes Refl
decEqQChar0 Cw Cw = Yes Refl
decEqQChar0 Cx Cx = Yes Refl
decEqQChar0 Cy Cy = Yes Refl
decEqQChar0 Cz Cz = Yes Refl
decEqQChar0 CA CA = Yes Refl
decEqQChar0 CB CB = Yes Refl
decEqQChar0 CC CC = Yes Refl
decEqQChar0 CD CD = Yes Refl
decEqQChar0 CE CE = Yes Refl
decEqQChar0 CF CF = Yes Refl
decEqQChar0 CG CG = Yes Refl
decEqQChar0 CH CH = Yes Refl
decEqQChar0 CI CI = Yes Refl
decEqQChar0 CJ CJ = Yes Refl
decEqQChar0 CK CK = Yes Refl
decEqQChar0 CL CL = Yes Refl
decEqQChar0 CM CM = Yes Refl
decEqQChar0 CN CN = Yes Refl
decEqQChar0 CO CO = Yes Refl
decEqQChar0 CP CP = Yes Refl
decEqQChar0 CQ CQ = Yes Refl
decEqQChar0 CR CR = Yes Refl
decEqQChar0 CS CS = Yes Refl
decEqQChar0 CT CT = Yes Refl
decEqQChar0 CU CU = Yes Refl
decEqQChar0 CV CV = Yes Refl
decEqQChar0 CW CW = Yes Refl
decEqQChar0 CX CX = Yes Refl
decEqQChar0 CY CY = Yes Refl
decEqQChar0 CZ CZ = Yes Refl

export
implementation DecEq (QChar v i) where
  decEq = decEqQChar0

export
decEqQChar : (x : QChar v i) -> (y : QChar w j) -> Dec (x = y)
decEqQChar {v} {w} {i} {j} x y with (decEq v w)
  decEqQChar {v} {w} {i} {j} x y | No neq = No (contra neq) where
    contra : {x' : QChar v' i'} -> {y' : QChar w' j'} -> (c1 : Not (v' = w')) -> Not (x' = y')
    contra c1 Refl = c1 Refl
  decEqQChar {v} {w = v} {i} {j} x y | Yes Refl with (decEq i j)
    decEqQChar {v} {w = v} {i} {j} x y | Yes Refl | No neq = No (contra neq) where
      contra : {x' : QChar v' i'} -> {y' : QChar v' j'} -> (c1 : Not (i' = j')) -> Not (x' = y')
      contra c1 Refl = c1 Refl
    decEqQChar {v} {w = v} {i} {j = i} x y | Yes Refl | Yes Refl = decEqQChar0 x y

---------------------------------------------------------------------------------------------------
-- [Cast] -----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
fromCharQChar : (x : Char) -> Maybe (Subset (CharKind, Nat) (QChar x))
fromCharQChar '_' = Just (Element (Sym, 0) C_)
fromCharQChar '\'' = Just (Element (Sym, 1) C')
fromCharQChar '.' = Just (Element (Sym, 2) Cstop)
fromCharQChar '0' = Just (Element (Num, 0) C0)
fromCharQChar '1' = Just (Element (Num, 1) C1)
fromCharQChar '2' = Just (Element (Num, 2) C2)
fromCharQChar '3' = Just (Element (Num, 3) C3)
fromCharQChar '4' = Just (Element (Num, 4) C4)
fromCharQChar '5' = Just (Element (Num, 5) C5)
fromCharQChar '6' = Just (Element (Num, 6) C6)
fromCharQChar '7' = Just (Element (Num, 7) C7)
fromCharQChar '8' = Just (Element (Num, 8) C8)
fromCharQChar '9' = Just (Element (Num, 9) C9)
fromCharQChar 'a' = Just (Element (Min1st, 0) Ca)
fromCharQChar 'b' = Just (Element (Min1st, 1) Cb)
fromCharQChar 'c' = Just (Element (Min1st, 2) Cc)
fromCharQChar 'd' = Just (Element (Min1st, 3) Cd)
fromCharQChar 'e' = Just (Element (Min1st, 4) Ce)
fromCharQChar 'f' = Just (Element (Min1st, 5) Cf)
fromCharQChar 'g' = Just (Element (Min1st, 6) Cg)
fromCharQChar 'h' = Just (Element (Min1st, 7) Ch)
fromCharQChar 'i' = Just (Element (Min1st, 8) Ci)
fromCharQChar 'j' = Just (Element (Min1st, 9) Cj)
fromCharQChar 'k' = Just (Element (Min2nd, 0) Ck)
fromCharQChar 'l' = Just (Element (Min2nd, 1) Cl)
fromCharQChar 'm' = Just (Element (Min2nd, 2) Cm)
fromCharQChar 'n' = Just (Element (Min2nd, 3) Cn)
fromCharQChar 'o' = Just (Element (Min2nd, 4) Co)
fromCharQChar 'p' = Just (Element (Min2nd, 5) Cp)
fromCharQChar 'q' = Just (Element (Min2nd, 6) Cq)
fromCharQChar 'r' = Just (Element (Min2nd, 7) Cr)
fromCharQChar 's' = Just (Element (Min2nd, 8) Cs)
fromCharQChar 't' = Just (Element (Min2nd, 9) Ct)
fromCharQChar 'u' = Just (Element (Min3rd, 0) Cu)
fromCharQChar 'v' = Just (Element (Min3rd, 1) Cv)
fromCharQChar 'w' = Just (Element (Min3rd, 2) Cw)
fromCharQChar 'x' = Just (Element (Min3rd, 3) Cx)
fromCharQChar 'y' = Just (Element (Min3rd, 4) Cy)
fromCharQChar 'z' = Just (Element (Min3rd, 5) Cz)
fromCharQChar 'A' = Just (Element (Maj1st, 0) CA)
fromCharQChar 'B' = Just (Element (Maj1st, 1) CB)
fromCharQChar 'C' = Just (Element (Maj1st, 2) CC)
fromCharQChar 'D' = Just (Element (Maj1st, 3) CD)
fromCharQChar 'E' = Just (Element (Maj1st, 4) CE)
fromCharQChar 'F' = Just (Element (Maj1st, 5) CF)
fromCharQChar 'G' = Just (Element (Maj1st, 6) CG)
fromCharQChar 'H' = Just (Element (Maj1st, 7) CH)
fromCharQChar 'I' = Just (Element (Maj1st, 8) CI)
fromCharQChar 'J' = Just (Element (Maj1st, 9) CJ)
fromCharQChar 'K' = Just (Element (Maj2nd, 0) CK)
fromCharQChar 'L' = Just (Element (Maj2nd, 1) CL)
fromCharQChar 'M' = Just (Element (Maj2nd, 2) CM)
fromCharQChar 'N' = Just (Element (Maj2nd, 3) CN)
fromCharQChar 'O' = Just (Element (Maj2nd, 4) CO)
fromCharQChar 'P' = Just (Element (Maj2nd, 5) CP)
fromCharQChar 'Q' = Just (Element (Maj2nd, 6) CQ)
fromCharQChar 'R' = Just (Element (Maj2nd, 7) CR)
fromCharQChar 'S' = Just (Element (Maj2nd, 8) CS)
fromCharQChar 'T' = Just (Element (Maj2nd, 9) CT)
fromCharQChar 'U' = Just (Element (Maj3rd, 0) CU)
fromCharQChar 'V' = Just (Element (Maj3rd, 1) CV)
fromCharQChar 'W' = Just (Element (Maj3rd, 2) CW)
fromCharQChar 'X' = Just (Element (Maj3rd, 3) CX)
fromCharQChar 'Y' = Just (Element (Maj3rd, 4) CY)
fromCharQChar 'Z' = Just (Element (Maj3rd, 5) CZ)
fromCharQChar  _  = Nothing
