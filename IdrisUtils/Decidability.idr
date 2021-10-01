module IdrisUtils.Decidability

%default total
%access public export

---------------------------------------------------------------------------------------------------
-- [Proposition] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

record Prop where
  constructor MkProp
  p       : Type
  q       : Type
  isP     : Dec p
  isQ     : Dec q
  p_sound : p -> Not q
  q_sound : q -> Not p

---------------------------------------------------------------------------------------------------
-- [Decidability] ---------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

||| A decidable property `p` either holds or its inverse property `q` holds.
data PDec : (pred : Prop) -> Type where
  Yes : (prf : p pred) -> PDec pred
  No  : (contra : q pred) -> PDec pred

||| A property is decidable and has a decision procedure.
record Decidable (pred : Prop) where
  constructor IsDecidable
  decP : PDec pred

---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

lemma_Dec_sound : PDec pred -> Basics.Dec (p pred)
lemma_Dec_sound (Yes prf) = Yes prf
lemma_Dec_sound {pred} (No contra) = No (\prf => q_sound pred contra prf)
