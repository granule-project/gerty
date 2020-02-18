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

class Check ext where
  checkExt :: Context -> ext -> Type -> Bool


instance Check NoExt where
  checkExt _ _ _ = False


check :: (Check ext, PrettyPrint ext, Synth ext) => Context -> Expr ext -> Type -> Bool

{--

G, x : A |- e <= B
--------------------------- abs
G |- (\x -> e) <= A -> B

-}
-- Curry style
check gamma (Abs x Nothing expr) (FunTy Nothing tyA tyB) =
  check ([(x, tyA)] ++ gamma) expr tyB

check gamma _ t@(FunTy (Just _) tyA tyB) =
  error $ "check on '" <> pprint t <> "' unsupported"

-- Church style
check gamma (Abs x (Just tyA') expr) (FunTy Nothing tyA tyB) | tyA == tyA' =
  check ([(x, tyA)] ++ gamma) expr tyB

check gamma (Ext e) t = checkExt gamma e t
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

class Synth ext where
  synthExt :: Context -> ext -> Maybe Type


instance Synth NoExt where
  synthExt _ _ = Nothing


synth :: (Check ext, PrettyPrint ext, Synth ext) => Context -> Expr ext -> Maybe Type

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
    Just t@(FunTy (Just _) tyA tyB) ->
      error $ "synth on '" <> pprint t <> "' unsupported (App branch)"
    Just (FunTy Nothing tyA tyB) ->
      -- Check the right-hand side
      if check gamma e2 tyA
        -- Yay!
        then Just tyB
        else error $ "Expecting (" ++ pprint e2 ++ ") to have type " ++ pprint tyA

    Just t ->
      error $ "Expecting (" ++ pprint e1 ++ ") to have function type but got " ++ pprint t

    Nothing ->
      error $ "Expecting (" ++ pprint e1 ++ ") to have function type."

synth gamma (Ext e) = synthExt gamma e

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
