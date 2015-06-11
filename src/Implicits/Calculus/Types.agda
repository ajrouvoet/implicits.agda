module Implicits.Calculus.Types where

open import Prelude hiding (lift; id)
open import Data.Fin.Substitution
import Data.Vec
  
data Type (ν : ℕ) : Set where
  tvar : (n : Fin ν) → Type ν
  _→'_ : Type ν → Type ν → Type ν
  _⇒_  : Type ν → Type ν → Type ν

data PolyType' (ν : ℕ) : (p : ℕ) → Set where
  mono : Type ν → PolyType' ν 0
  ∀'   : ∀ {p} → PolyType' (suc ν) p → PolyType' ν (suc p)

PolyType : ℕ → ℕ → Set
PolyType p ν = PolyType' ν p

PType : ℕ → Set
PType ν = ∃ λ p → PolyType p ν

ptype : ∀ {p ν} → PolyType p ν → PType ν
ptype x = , x

module TypeSubst where
  module TypeApp {T} (l : Lift T Type) where
    open Lift l hiding (var)

    infixl 8 _/_

    _/_ : ∀ {m n} → Type m → Sub T m n → Type n
    tvar x   / σ = lift (lookup x σ)
    (a →' b) / σ = (a / σ) →' (b / σ)
    (a ⇒ b)  / σ = (a / σ) ⇒ (b / σ)

    open Application (record { _/_ = _/_ }) using (_/✶_)

  typeSubst : TermSubst Type
  typeSubst = record { var = tvar; app = TypeApp._/_ }

  open TermSubst typeSubst public hiding (var)

  infix 8 _[/_]

  -- Shorthand for single-variable type substitutions
  _[/_] : ∀ {n} → Type (suc n) → Type n → Type n
  a [/ b ] = a / sub b
  
module TypeLemmas where
  open import Data.Fin.Substitution.Lemmas
  open TypeSubst
  open import Data.Star using (Star; ε; _◅_)
  
  typeLemmas : TermLemmas Type
  typeLemmas = record { termSubst = TypeSubst.typeSubst; app-var = refl ; /✶-↑✶ = Lemma./⋆-↑⋆ }
    where
      module Lemma {T₁ T₂} {lift₁ : Lift T₁ Type} {lift₂ : Lift T₂ Type} where
      
        open Lifted lift₁ using () renaming (_↑✶_ to _↑✶₁_; _/✶_ to _/✶₁_)
        open Lifted lift₂ using () renaming (_↑✶_ to _↑✶₂_; _/✶_ to _/✶₂_)

        postulate /⋆-↑⋆ : ∀ {m n} (σs₁ : Subs T₁ m n) (σs₂ : Subs T₂ m n) → 
                          (∀ k x → tvar x /✶₁ σs₁ ↑✶₁ k ≡ tvar x /✶₂ σs₂ ↑✶₂ k) → 
                          ∀ k t → t /✶₁ σs₁ ↑✶₁ k ≡ t /✶₂ σs₂ ↑✶₂ k

  open TermLemmas typeLemmas public hiding (var)

  -- The above lemma /✶-↑✶ specialized to single substitutions
  /-↑⋆ : ∀ {T₁ T₂} {lift₁ : Lift T₁ Type} {lift₂ : Lift T₂ Type} →
         let open Lifted lift₁ using () renaming (_↑⋆_ to _↑⋆₁_; _/_ to _/₁_)
             open Lifted lift₂ using () renaming (_↑⋆_ to _↑⋆₂_; _/_ to _/₂_)
         in
         ∀ {n k} (ρ₁ : Sub T₁ n k) (ρ₂ : Sub T₂ n k) →
         (∀ i x → tvar x /₁ ρ₁ ↑⋆₁ i ≡ tvar x /₂ ρ₂ ↑⋆₂ i) →
          ∀ i a → a /₁ ρ₁ ↑⋆₁ i ≡ a /₂ ρ₂ ↑⋆₂ i
  /-↑⋆ ρ₁ ρ₂ hyp i a = /✶-↑✶ (ρ₁ ◅ ε) (ρ₂ ◅ ε) hyp i a

open TypeSubst public using () renaming (_/_ to _tp/tp_; _[/_] to _tp[/tp_])

-- substitute for the first bound variable
-- postulate _poly[/tp_] : ∀ {p m} → PolyType (suc p) m → Type m → PolyType p m
-- substitute for the first free variable
postulate _free[/tp_] : ∀ {p m} → PolyType p (suc m) → Type m → PolyType p m
