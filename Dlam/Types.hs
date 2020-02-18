module Dlam.Types where

import Dlam.Syntax
import Dlam.PrettyPrint
import Dlam.Semantics (substituteType)

import Data.Maybe (mapMaybe)
import Data.List (intercalate)

{-

*************************************************************
Declarative specification of the simply-typed lambda calculus
*************************************************************
Recall contexts are like lists of variable-type assumptions


G ::=  G, x : A | .

       (x : A) in G
var ----------------------
       G |- x : A

     G |- e1 : A -> B      G |- e2 : A
app ---------------------------------------
    G |- e1 e2 : B

      G, x : A |- e : B
abs ------------------------
      G |- \x -> e : A -> B

-}

-- Represent contexts as lists
type Context = [(Identifier, Type)]

{-

Bidirectional checking
*********************************
G |- e <= A    check
**********************************
-}

check :: Context -> Expr PCF -> Type -> Bool

{--

G, x : A |- e <= B
--------------------------- abs
G |- (\x -> e) <= A -> B

-}
-- Curry style
check gamma (Abs x Nothing expr) (FunTy tyA tyB) =
  check ([(x, tyA)] ++ gamma) expr tyB

-- Church style
check gamma (Abs x (Just tyA') expr) (FunTy tyA tyB) | tyA == tyA' =
  check ([(x, tyA)] ++ gamma) expr tyB

--- PCF rules
check gamma (Ext (Fix e)) t = check gamma e (FunTy t t)

check gamma (Ext (NatCase e e1 (x,e2))) t =
  check gamma e NatTy &&
  check gamma e1 t &&
  check ([(x,NatTy)] ++ gamma) e2 t

check gamma (Ext (Pair e1 e2)) (ProdTy t1 t2) =
  check gamma e1 t1 &&
  check gamma e2 t2

check gamma (Ext (Pair _ _)) _ = False

check gamma (Ext (Fst e)) t =
  case synth gamma e of
    Just (ProdTy t1 t2) -> t == t1
    _ -> False

check gamma (Ext (Snd e)) t =
  case synth gamma e of
    Just (ProdTy t1 t2) -> t == t2
    _ -> False

check gamma (Ext (Inl e)) (SumTy t1 t2) = check gamma e t1
check gamma (Ext (Inl e)) _ = False

check gamma (Ext (Inr e)) (SumTy t1 t2) = check gamma e t2
check gamma (Ext (Inr e)) _ = False

check gamma (Ext (Case e (x,e1) (y,e2))) t =
  case synth gamma e of
    Just (SumTy t1 t2) ->
      check ([(x,t1)] ++ gamma) e1 t &&
      check ([(y,t2)] ++ gamma) e2 t
    _ -> False

-- Polymorphic lambda calculus
check gamma (TyAbs alpha e) (Forall alpha' tau)
  | alpha == alpha' =
    -- find all free variables in gamma which have alpha free inside of their type assumption
    case mapMaybe (\(id, t) -> if alpha `elem` freeVars t then Just id else Nothing) gamma of
      -- side condition is true
      [] -> check gamma e tau
      vars -> error $ "Free variables " <> intercalate "," vars
                  <> " use bound type variable `" <> alpha <> "`"

  | otherwise =
    error $ "Term-level type abstraction on `" <> alpha
          <> "` does not match name of type abstraction `" <> alpha' <> "`"

{--

G |- e => A'   A' == A
--------------------------- synthCheck
G |- e <= A

--}

check gamma expr tyA =
  case synth gamma expr of
    Nothing -> False
    Just tyA' -> tyA == tyA'

{-
Bidirectional synthesis
**********************************
 G |- e => A    synth
**********************************
-}

synth :: Context -> Expr PCF -> Maybe Type

{-

(x : A) in G
--------------- var
G |- x => A

-}

synth gamma (Var x) =
  lookup x gamma

{-

The following is a special form of (app) which
is useful for doing top-level definitions in our style,
which are of the form (\x -> e) (e' : A).

This is equivalent to combining the synthesis for general
application (below, (app) rule) with the synthesis rule we can have
if we have Church-style syntax

      G, x : A |- e => B
      -------------------------------------- abs-Church
      G |- (\(x : A) -> e) => A -> B

i.e., we know we have a signature for the argument.

-}

-- app (special for form of top-level definitions)
synth gamma (App (Abs x Nothing e1) (Sig e2 tyA)) =
  if check gamma e2 tyA
    then synth ([(x, tyA)] ++ gamma) e1
    else error $ "Expecting (" ++ pprint e2 ++ ") to have type " ++ pprint tyA


-- abs-Church (actually rule)
synth gamma (Abs x (Just tyA) e) =
  synth ((x, tyA) : gamma) e

-- Type checking a type speciaisation
synth gamma (App e (TyEmbed tau')) =
  case synth gamma e of
    Just (Forall alpha tau) -> Just $ substituteType tau (alpha, tau')
    Just t -> error $ "Expecting polymorphic type but got `" <> pprint t <> "`"
    Nothing -> error $ "Expecting polymorphic type but didn't get anything."

{-

  G |- e1 => A -> B    G |- e2 <= A
  ----------------------------------- app
  G |- e1 e2 => B

-}

synth gamma (App e1 e2) =
  -- Synth the left-hand side
  case synth gamma e1 of
    Just (FunTy tyA tyB) ->
      -- Check the right-hand side
      if check gamma e2 tyA
        -- Yay!
        then Just tyB
        else error $ "Expecting (" ++ pprint e2 ++ ") to have type " ++ pprint tyA

    Just t ->
      error $ "Expecting (" ++ pprint e1 ++ ") to have function type but got " ++ pprint t

    Nothing ->
      error $ "Expecting (" ++ pprint e1 ++ ") to have function type."

-- PCF rules
synth gamma (Ext Zero) =
  Just NatTy

synth gamma (Ext Succ) =
  Just (FunTy NatTy NatTy)

synth gamma (Ext (NatCase e e1 (x,e2))) =
  if check gamma e NatTy then
    case synth gamma e1 of
      Just t ->
        if check ([(x,NatTy)] ++ gamma) e2 t
          then Just t
          else error $ "Expecting (" ++ pprint e2 ++ ") to have type " ++ pprint t
      Nothing ->
        (case synth ([(x,NatTy)] ++ gamma) e2 of
          Just t ->
            if check gamma e1 t
              then Just t
              else error $ "Expecting (" ++ pprint e1 ++ ") to have type " ++ pprint t
          Nothing -> error $ "Could not synth types for " ++ pprint e1 ++ ", " ++ pprint e2)
  else error $ "Expecting (" ++ pprint e ++ ") to have type " ++ pprint NatTy

synth gamma (Ext (Fix e)) =
  case synth gamma e of
    Just (FunTy t1 t2) ->
      if t1 == t2 then Just t1
      else error $ "Expecting (" ++ pprint e ++ ") to have function type with equal domain/range but got " ++ pprint (FunTy t1 t2)
    Just t -> error $ "Expecting (" ++ pprint e ++ ") to have function type with equal domain/range but got " ++ pprint t
    Nothing -> error $ "Expecting (" ++ pprint e ++ ") to have function type with equal domain/range"

synth gamma (Ext (Pair e1 e2)) =
  case synth gamma e1 of
    Just t1 ->
      case synth gamma e2 of
        Just t2 -> Just (ProdTy t1 t2)
        Nothing -> error $ "Could not synth type for " ++ pprint e2
    Nothing -> error $ "Could not synth type for " ++ pprint e1

synth gamma (Ext (Fst e)) =
  case synth gamma e of
    Just (ProdTy t1 t2) -> Just t1
    Just t -> error $ "Expecting (" ++ pprint e ++ ") to have product type but got " ++ pprint t
    Nothing -> error $ "Could not synth type for " ++ pprint e

synth gamma (Ext (Snd e)) =
  case synth gamma e of
    Just (ProdTy t1 t2) -> Just t2
    Just t -> error $ "Expecting (" ++ pprint e ++ ") to have product type but got " ++ pprint t
    Nothing -> error $ "Could not synth type for " ++ pprint e

synth gamma (Ext (Case e (x,e1) (y,e2))) =
  case synth gamma e of
    Just (SumTy t1 t2) -> (
      case synth ([(x,t1)] ++ gamma) e1 of
        Just t ->
          if check ([(y,t2)] ++ gamma) e2 t
            then Just t
            else error $ "Expecting (" ++ pprint e2 ++ ") to have type " ++ pprint t
        Nothing -> (
          case synth ([(y,t2)] ++ gamma) e2 of
            Just t ->
              if check ([(x,t1)] ++ gamma) e1 t
                then Just t
                else error $ "Expecting (" ++ pprint e1 ++ ") to have type " ++ pprint t
            Nothing -> error $ "Could not synth types for " ++ pprint e1 ++ ", " ++ pprint e2
          )
        )
    Just t -> error $ "Expecting (" ++ pprint e ++ ") to have sum type but got " ++ pprint t
    Nothing -> error $ "Could not synth type for " ++ pprint e


{-

  G |- e <= A
  ------------------- checkSynth
  G |- (e : A) => A

-}

-- checkSynth
synth gamma (Sig e ty) =
  if check gamma e ty
    then Just ty
    else error $ "Trying to check (" ++ pprint e ++ ") against " ++ pprint ty

-- catch all (cannot synth here)
synth gamma e =
   error $ "Cannot synth the type for " ++ pprint e
