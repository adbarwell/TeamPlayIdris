module IdrisUtils.Data.Sign

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Definition] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

data Sign : Type where
  Positive : Sign
  Negative : Sign

---------------------------------------------------------------------------------------------------
-- [Operations] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

opposite : Sign -> Sign
opposite Negative = Positive
opposite Positive = Negative

(*) : Sign -> Sign -> Sign
(*) Positive s = s
(*) Negative s = opposite s