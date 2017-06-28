module Impure.STLCRef.Semantics.Unsafe where

{-
  Definitional interpreter for STLCRef
-}

open import Prelude

open import Impure.STLCRef.Syntax.Untyped hiding (Val; Store)
open import Impure.STLCRef.Welltyped

open import Category.Monad.Identity
open import Category.Monad.Partiality

open import Data.Maybe renaming (monadT to ErrorT)
open import Data.Unit
open import Data.Vec hiding (_>>=_)
open import Data.List
open import Data.List.Prefix

open Workaround hiding (_>>=_)

mutual
  data Val : Set where
    unit : Val
    ƛ    : ∀ {n} → Type → (e : Exp (suc n)) → Env n → Val
    loc  : (i : ℕ) → Val

  Env : ℕ → Set
  Env n = Vec Val n

toTerm : Val → ∃ λ n → Env n × Exp n
toTerm unit = zero , [] , unit
toTerm (ƛ A e E) = _ , E ,  ƛ A e
toTerm (loc i) = zero , [] , loc i

Store : Set
Store = List Val

-- postulated monad that threads a readonly environment, store and propagates
-- semantic errors
EvalM : Set → Set₁
EvalM A = ℕ → Store → (Maybe A) ⊥P

-- monad operations that need to be implemented
postulate _>>=_  : ∀ {A B} → EvalM A → (A → EvalM B) → EvalM B
postulate return : ∀ {A} → A → EvalM A
postulate error  : ∀ {A} → EvalM A
postulate timeout : ∀ {A} → EvalM A
postulate readStore : ℕ → EvalM Val
postulate writeStore : ℕ → Val → EvalM ⊤
postulate allocStore : Val → EvalM ⊤

-- NOTE: In a substitution free semantics we have to be able to
-- switch environments when we call a function; ReaderT is not enough

pattern S n = suc n
pattern Z = zero

eval : ∀ {n} → ℕ → Env n → Exp n → EvalM Val
eval Z _ _ = timeout
eval (S n) E unit = return unit
eval (S n) E (var x) = return $ lookup x E
eval (S n) E (loc x) = readStore x
eval (S n) E (ƛ A e) = return (ƛ A e E)
eval (S n) E (f · e) =
  eval n E f >>= λ{
    (ƛ _ clos Eclos) →
      eval n E e >>= λ v →
      eval n (v ∷ Eclos) clos
    ; otherwise → error
  }
eval (S n) E (ref e) =
  eval n E e >>= λ v →
  allocStore v >>= λ _ →
  return unit
eval (S n) E (! e) =
  eval n E e >>= λ{
    (loc i) →
      readStore i
    ; otherwise → error
  }
eval (S n) E (e ≔ d) =
  eval n E e >>= λ{
  (loc i) →
    eval n E d >>= λ v →
    writeStore i v >>= λ _ →
    return unit
  ; otherwise → error
  }
