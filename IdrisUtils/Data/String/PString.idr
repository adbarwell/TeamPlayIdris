module IdrisUtils.Data.String.PString

import public IdrisUtils.Data.String.QString

%default total

---------------------------------------------------------------------------------------------------
-- [Definitions] ----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

public export
data PString : Type where
  MkString : QString str -> PString

---------------------------------------------------------------------------------------------------
-- [DecEq] ----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
decEqPString : (x,y : PString) -> Dec (x = y)
decEqPString (MkString x) (MkString y) with (decEqQString x y)
  decEqPString (MkString x) (MkString y) | No neq = No (\Refl => neq Refl)
  decEqPString (MkString x) (MkString x) | Yes Refl = Yes Refl

export
implementation DecEq PString where
  decEq = decEqPString

---------------------------------------------------------------------------------------------------
-- [Cast] -----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
toString : PString -> String
toString (MkString {str} _) = pack str

export
implementation Cast PString String where
  cast = toString

export
fromString : (str : String) -> Maybe PString
fromString str = do
  qstr <- fromString str
  pure (MkString qstr)

export Cast String PString where
  cast str =
    case PString.fromString str of
      Nothing => MkString Nil
      Just pstr => pstr

---------------------------------------------------------------------------------------------------
-- [Show] -----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

export
implementation Show PString where
  show = toString

---------------------------------------------------------------------------------------------------
-- [Total Ordering] -------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- [Definition] -----------------------------------------------------------------------------------

public export
data LTPString : (x,y : PString) -> Type where
  IsLTPString : (p : LTQString x y) -> LTPString (MkString x) (MkString y)

-- [Uninhabited] ----------------------------------------------------------------------------------

implementation Uninhabited (MkString Nil = MkString ((::) y ys)) where
  uninhabited Refl impossible

-- [Asymmetry, Transitivity, and Trichotomy] ------------------------------------------------------

export
asymLTPString : (x,y : PString) -> LTPString x y -> Not (LTPString y x)
asymLTPString (MkString x) (MkString y) (IsLTPString p) (IsLTPString q) = asymLTQString x y p q

export
irrLTPString : (x : PString) -> Not (LTPString x x)
irrLTPString x p = asymLTPString x x p p

export
transLTPString : (x,y,z : PString)
              -> LTPString x y
              -> LTPString y z
              -> LTPString x z
transLTPString (MkString x) (MkString y) (MkString z) (IsLTPString p) (IsLTPString q) =
  IsLTPString (transLTQString x y z p q)

export
contra : (c1 : Not (MkChar x' = MkChar y'))
      -> Not (MkString ((::) x' xs') = MkString ((::) y' ys'))
contra c1 Refl = c1 Refl

export
contra2 : {xs : QString v}
       -> {ys : QString w}
       -> (c1 : Not (MkString xs = MkString ys))
       -> Not (MkString ((::) x xs) = MkString ((::) x ys))
contra2 c1 Refl = c1 Refl

export
trichoLTPString' : (xs : QString v)
                -> (ys : QString w)
                -> Trichotomy (PropEqSetoid PString PString.decEqPString)
                              LTPString
                              (MkString xs)
                              (MkString ys)
trichoLTPString' Nil Nil =
  IsEq (irrLTPString (MkString Nil))
trichoLTPString' Nil ((::) y ys) =
  IsBinR_xRy (IsLTPString IsLTQStringNil)
             (asymLTPString (MkString Nil) (MkString ((::) y ys))
                            (IsLTPString IsLTQStringNil))
             absurd
trichoLTPString' ((::) x xs) Nil =
  IsBinR_yRx (IsLTPString IsLTQStringNil)
             (asymLTPString (MkString Nil) (MkString ((::) x xs))
                            (IsLTPString IsLTQStringNil))
             (absurd . sym)
trichoLTPString' ((::) x xs) ((::) y ys) =
  case trichoLTPChar (MkChar x) (MkChar y) of
    IsEq irr =>
      case trichoLTPString' xs ys of
        IsEq irr' => IsEq (irrLTPString (MkString ((::) x xs)))
        IsBinR_xRy (IsLTPString p) nq neq =>
          IsBinR_xRy (IsLTPString (IsLTQStringRest p))
                     (asymLTPString (MkString ((::) x xs))
                                    (MkString ((::) x ys))
                                    (IsLTPString (IsLTQStringRest p)))
                     (contra2 neq)
        IsBinR_yRx (IsLTPString q) np neq =>
          IsBinR_yRx (IsLTPString (IsLTQStringRest q))
                     (asymLTPString (MkString ((::) x ys))
                                    (MkString ((::) x xs))
                                    (IsLTPString (IsLTQStringRest q)))
                     (contra2 neq)
    IsBinR_xRy (IsLTPChar p) nq neq =>
      IsBinR_xRy (IsLTPString (IsLTQStringChar p))
                 (asymLTPString (MkString ((::) x xs))
                                (MkString ((::) y ys))
                                (IsLTPString (IsLTQStringChar p)))
                 (\Refl => neq Refl)
    IsBinR_yRx (IsLTPChar q) np neq =>
      IsBinR_yRx (IsLTPString (IsLTQStringChar q))
                 (asymLTPString (MkString ((::) y ys))
                                (MkString ((::) x xs))
                                (IsLTPString (IsLTQStringChar q)))
                 (contra neq)

export
trichoLTPString : (x,y : PString)
               -> Trichotomy (PropEqSetoid PString PString.decEqPString) LTPString x y
trichoLTPString (MkString Nil) (MkString Nil) = IsEq (irrLTPString (MkString Nil))
trichoLTPString (MkString Nil) (MkString ((::) y ys)) =
  IsBinR_xRy (IsLTPString IsLTQStringNil)
             (asymLTPString (MkString Nil) (MkString ((::) y ys))
                            (IsLTPString IsLTQStringNil))
             absurd
trichoLTPString (MkString ((::) x xs)) (MkString Nil) =
  IsBinR_yRx (IsLTPString IsLTQStringNil)
             (asymLTPString (MkString Nil) (MkString ((::) x xs))
                            (IsLTPString IsLTQStringNil))
             (absurd . sym)
trichoLTPString (MkString ((::) x xs)) (MkString ((::) y ys)) =
  case trichoLTPChar (MkChar x) (MkChar y) of
    IsEq irr =>
      case trichoLTPString' xs ys of
        IsEq irr' => IsEq (irrLTPString (MkString ((::) x xs)))
        IsBinR_xRy (IsLTPString p) nq neq =>
          IsBinR_xRy (IsLTPString (IsLTQStringRest p))
                     (asymLTPString (MkString ((::) x xs))
                                    (MkString ((::) x ys))
                                    (IsLTPString (IsLTQStringRest p)))
                     (contra2 neq)
        IsBinR_yRx (IsLTPString q) np neq =>
          IsBinR_yRx (IsLTPString (IsLTQStringRest q))
                     (asymLTPString (MkString ((::) x ys))
                                    (MkString ((::) x xs))
                                    (IsLTPString (IsLTQStringRest q)))
                     (contra2 neq)
    IsBinR_xRy (IsLTPChar p) nq irr =>
      IsBinR_xRy (IsLTPString (IsLTQStringChar p))
                 (asymLTPString (MkString ((::) x xs))
                                (MkString ((::) y ys))
                                (IsLTPString (IsLTQStringChar p)))
                 (\Refl => irr Refl)
    IsBinR_yRx (IsLTPChar q) np irr =>
      IsBinR_yRx (IsLTPString (IsLTQStringChar q))
                 (asymLTPString (MkString ((::) y ys))
                                (MkString ((::) x xs))
                                (IsLTPString (IsLTQStringChar q)))
                 (contra irr)

-- [Decision Procedure] ---------------------------------------------------------------------------

export
decLTPString : (x,y : PString) -> Dec (LTPString x y)
decLTPString x y with (trichoLTPString x y)
  decLTPString x x | IsEq irr = No irr
  decLTPString x y | IsBinR_xRy p nq neq = Yes p
  decLTPString x y | IsBinR_yRx q np neq = No np


-- [Total Ordering (General Setoid)] --------------------------------------------------------------

export
StrictTotalOrderingTPString : StrictTotalOrderingT PString
                                                   (PropEqSetoid PString PString.decEqPString)
StrictTotalOrderingTPString =
  MkSTOrderingT LTPString asymLTPString transLTPString trichoLTPString decLTPString

-- [Singleton] ------------------------------------------------------------------------------------

export
singLTPString : (x,y : PString) -> (p,q : LTPString x y) -> p = q
singLTPString (MkString x) (MkString y) (IsLTPString p) (IsLTPString q) with (singLTQString x y p q)
  singLTPString (MkString x) (MkString y) (IsLTPString p) (IsLTPString p) | Refl = Refl


-- [Total Ordering with Singleton] ----------------------------------------------------------------

export
StrictTotalOrderingSPString : StrictTotalOrderingS PString
                                                   (PropEqSetoid PString PString.decEqPString)
StrictTotalOrderingSPString = MkSTOrderingS StrictTotalOrderingTPString singLTPString

-- [Total Ordering] -------------------------------------------------------------------------------

export
StrictTotalOrderingPString : StrictTotalOrdering PString
StrictTotalOrderingPString = MkSTOrdering PString.decEqPString StrictTotalOrderingSPString

---------------------------------------------------------------------------------------------------
-- [Properties] -----------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- [Decidability] ---------------------------------------------------------------------------------

-- This should all be derivable now that we have the new total ordering definition.
-- One easy way of doing this would be to have one master function that you plug your types and
-- orders into.

export
lemma_LT_sound : (x,y : PString) -> LTPString x y -> Not (LTE StrictTotalOrderingPString y x)
lemma_LT_sound (MkString x) (MkString x) (IsLTPString p) IsEq = irrLTQString x p
lemma_LT_sound (MkString x) (MkString y) (IsLTPString p) (IsLT (IsLTPString q)) =
  asymLTQString x y p q

export
lemma_LTE_sound : (x,y : PString) -> LTE StrictTotalOrderingPString y x -> Not (LTPString x y)
lemma_LTE_sound x x IsEq q = irrLTPString x q
lemma_LTE_sound x y (IsLT p) q = asymLTPString y x p q

export
PropPString : (x,y : PString) -> Prop
PropPString x y = MkProp (LTPString x y) (LTE StrictTotalOrderingPString y x)
                         (decLTPString x y) (decLTE StrictTotalOrderingPString y x)
                         (lemma_LT_sound x y) (lemma_LTE_sound x y)

export
decPLTPString : (x,y : PString) -> PDec (PropPString x y)
decPLTPString x y with (trichoLTPString x y)
  decPLTPString x x | IsEq irr = No IsEq
  decPLTPString x y | IsBinR_xRy p nq neq = Yes p
  decPLTPString x y | IsBinR_yRx q np neq = No (IsLT q)

export
DecidablePString : (x,y : PString) -> Decidable (PropPString x y)
DecidablePString x y = IsDecidable (decPLTPString x y)

export
implementation StrictTotalOrder PString where
  theOrder = StrictTotalOrderingPString

export
implementation LTSound PString where
  lt_sound {x} p IsEq = irrLTPString x p
  lt_sound {x} {y} p (IsLT q) = asymLTPString x y p q

  gte_sound {x} IsEq p = irrLTPString x p
  gte_sound {x} {y} (IsLT q) p = asymLTPString x y p q
