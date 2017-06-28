module Impure.STLCRef.Semantics.Unsafe where

{-
  Definitional interpreter for STLCRef
-}

open import Prelude
open import Impure.STLCRef.Syntax.Untyped hiding (Val; Store)

open import Category.Monad.Identity
open import Data.Maybe renaming (monadT to ErrorT)
open import Data.Unit
open import Data.Vec hiding (_>>=_)
open import Data.List

mutual
  data Val : Set where
    unit : Val
    ƛ    : ∀ {n} → (e : Exp (suc n)) → Env n → Val
    loc  : (i : ℕ) → Val

  Env : ℕ → Set
  Env n = Vec Val n

Store : ℕ → Set
Store n = List Val

-- postulated monad that threads a readonly environment, store and propagates
-- semantic errors
postulate EvalM : Set → Set

-- monad operations that need to be implemented
postulate _>>=_  : ∀ {A B} → EvalM A → (A → EvalM B) → EvalM B
postulate return : ∀ {A} → A → EvalM A
postulate error  : ∀ {A} → EvalM A
postulate readStore : ℕ → EvalM Val
postulate writeStore : ℕ → Val → EvalM ⊤
postulate allocStore : Val → EvalM ⊤

-- NOTE: In a substitution free semantics we have to be able to
-- switch environments when we call a function; ReaderT is not enough

{-# NON_TERMINATING #-}
eval : ∀ {n} → Env n → Exp n → EvalM Val
eval E unit = return unit
eval E (var x) = return $ lookup x E
eval E (loc x) = readStore x
eval E (ƛ x e) = return (ƛ e E)
eval E (f · e) =
  eval E f >>= λ{
    (ƛ clos Eclos) →
      eval E e >>= λ v →
      eval (v ∷ Eclos) clos
    ; otherwise →
      error
  }
eval E (ref e) =
  eval E e >>= λ v →
  allocStore v >>= λ _ →
  return unit
eval E (! e) =
  eval E e >>= λ{
    (loc i) →
      readStore i
    ; otherwise →
      error
  }
eval E (e ≔ d) =
  eval E e >>= λ{
  (loc i) →
    eval E d >>= λ v →
    writeStore i v >>= λ _ →
    return unit
  ; otherwise →
    error
  }
