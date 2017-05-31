module SystemF.BigStep.Extrinsic.Semantics where

open import Prelude hiding (⊥; id)
open import Function as Fun using ()
open import Data.List hiding ([_]; monad)
open import Data.List.Properties as ListProp using ()
open import Data.Fin.Substitution
open import Extensions.List

open import SystemF.BigStep.Types
open import SystemF.BigStep.Extrinsic.Terms
open import SystemF.BigStep.Extrinsic.Welltyped

open import Level as Lev using ()
open import Data.Maybe
open import Category.Monad
open RawMonad (monad {f = Lev.zero})

-- quadratic return through the layered monad
pattern just² x = just (just x)

-- substitution-free semantics in double-layered maybe monad;
-- distinguishing semantic errors from timeouts
-- (the code is spaced to be read side-by-side with the safety proof)
_⊢_⇓_ : ∀ (μ : Env) → Term → ℕ → Maybe (Maybe Val)
μ ⊢ x ⇓ zero = nothing
μ ⊢ unit ⇓ (suc n) = just² unit
μ ⊢ ƛ t ⇓ (suc n) = just² (clos μ t)
μ ⊢ Λ t ⇓ (suc n) = just² (tclos μ t )

μ ⊢ f · e ⇓ (suc n) with (μ ⊢ f ⇓ n) | μ ⊢ e ⇓ n
-- timeout
... | nothing | _ = nothing
... | just _ | nothing = nothing
-- success
... | just² (clos μ' t) | just² v = (v ∷ μ') ⊢ t ⇓ n
-- semantic errors & semantic error propagation
... | _ | _ = just nothing

μ ⊢ t [-] ⇓ (suc n) with (μ ⊢ t ⇓ n)
-- timeout
... | nothing = nothing
-- success
... | just² (tclos μ' t') = μ' ⊢ t' ⇓ n
-- semantic error (propagation)
... | _ = just nothing

μ ⊢ var x ⇓ (suc n) = just (maybe-lookup x μ)

{-
module DelayMonad where

  open import Coinduction
  open import Category.Monad.Partiality
  open import Data.Maybe

  module _ where
    open Workaround

    _⊢lookup_ : Env → ℕ → Maybe Val
    [] ⊢lookup n = nothing
    (x ∷ μ) ⊢lookup zero = just x
    (x ∷ μ) ⊢lookup suc n = μ ⊢lookup n

    ret : ∀ {a} {A : Set a} → A → (Maybe A) ⊥P
    ret x = now (just x)

    -- substitution free semantics for SystemF
    _⊢_⇓P : ∀ (μ : Env) → Term → (Maybe Val) ⊥P
    μ ⊢ unit ⇓P = ret unit
    μ ⊢ ƛ t ⇓P = ret (clos μ t)
    μ ⊢ Λ t ⇓P = ret (tclos μ t )
    μ ⊢ f · e ⇓P = μ ⊢ f ⇓P >>= λ{
        (just (clos μ' t)) → μ ⊢ e ⇓P >>= (λ{
          (just v) → later (♯ ((v ∷ μ') ⊢ t ⇓P))
          ; nothing → now nothing
        }) ;
        _ → now nothing
      }
    μ ⊢ t [-] ⇓P = μ ⊢ t ⇓P >>= λ{
        (just (tclos μ' t')) →  later (♯ (μ' ⊢ t' ⇓P)) ;
        _ → now nothing
      }
    μ ⊢ var x ⇓P = now (μ ⊢lookup x)

    _⊢_⇓ : ∀ (μ : Env) → Term → (Maybe Val) ⊥
    μ ⊢ t ⇓ = ⟦ μ ⊢ t ⇓P ⟧P

{-}
  open import Category.Monad.Partiality.All
  open Alternative

  {-}
  module Compositional where
    private
      module Eq = Equality (_≡_)

    open import Level as Level
    open import Category.Monad
    open Eq hiding (_⇓)
    open RawMonad (monad {f = Level.zero})

    _·⇓_ : ∀ (f e : Val ⊥) → Val ⊥
    f ·⇓ e = f >>= λ{ (clos x t) → {!!} ; _ → now error }

    ·-comp : ∀ {μ f e} → (μ ⊢ f · e ⇓) ≅ ((μ ⊢ f ⇓) ·⇓ (μ ⊢ e ⇓))
    ·-comp = {!!}
  -}

  module Safety where

    _⊢_⇓okP : ∀ {n}{Γ : Ctx n}{μ : Env}{t a} → Γ ⊢ μ → Γ ⊢ t ∶ a → AllP (λ v → ⊢̬ v ∶ a) (μ ⊢ t ⇓)
    μ ⊢ unit ⇓okP = now unit
    μ ⊢ ƛ a t₁ ⇓okP = now (clos t₁ μ)
    μ ⊢ var x ⇓okP = now {!!}
    μ ⊢ f · e ⇓okP = {!μ ⊢ f ⇓okP!}
    μ ⊢ Λ t₁ ⇓okP = {!!}
    μ ⊢ t [ b ] ⇓okP = {!!}
-}
-}
