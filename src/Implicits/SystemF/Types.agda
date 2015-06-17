module Implicits.SystemF.Types where

open import Prelude hiding (lift)
open import Data.Fin.Substitution
open import Extensions.Substitution
open import Data.Star using (Star; ε; _◅_)
  
data Type (ν : ℕ) : Set where
  tvar : (n : Fin ν) → Type ν
  _→'_ : Type ν → Type ν → Type ν
  ∀'   : Type (suc ν) → Type ν

module TypeSubst where
  module TypeApp {T} (l : Lift T Type) where
    open Lift l hiding (var)

    infixl 8 _/_

    _/_ : ∀ {m n} → Type m → Sub T m n → Type n
    tvar x   / σ = lift (lookup x σ)
    (a →' b) / σ = (a / σ) →' (b / σ)
    ∀' a     / σ = ∀' (a / σ ↑)

    open Application (record { _/_ = _/_ }) using (_/✶_)

    →'-/✶-↑✶ : ∀ k {m n a b} (ρs : Subs T m n) →
               (a →' b) /✶ ρs ↑✶ k ≡ (a /✶ ρs ↑✶ k) →' (b /✶ ρs ↑✶ k)
    →'-/✶-↑✶ k ε        = refl
    →'-/✶-↑✶ k (ρ ◅ ρs) = cong₂ _/_ (→'-/✶-↑✶ k ρs) refl

    ∀'-/✶-↑✶ : ∀ k {m n a} (ρs : Subs T m n) →
               (∀' a) /✶ ρs ↑✶ k ≡ ∀' (a /✶ ρs ↑✶ (1 N+ k))
    ∀'-/✶-↑✶ k ε        = refl
    ∀'-/✶-↑✶ k (ρ ◅ ρs) = cong₂ _/_ (∀'-/✶-↑✶ k ρs) refl

  typeSubst : TermSubst Type
  typeSubst = record { var = tvar; app = TypeApp._/_ }

  open TermSubst typeSubst public hiding (var)

  infix 8 _[/_]

  -- Shorthand for single-variable type substitutions
  _[/_] : ∀ {n} → Type (suc n) → Type n → Type n
  a [/ b ] = a / sub b

module TypeLemmas where
  open TypeSubst
  open import Data.Fin.Substitution.Lemmas
  open import Data.Star using (Star; ε; _◅_)
  
  typeLemmas : TermLemmas Type
  typeLemmas = record { termSubst = TypeSubst.typeSubst; app-var = refl ; /✶-↑✶ = Lemma./✶-↑✶ }
    where
      module Lemma {T₁ T₂} {lift₁ : Lift T₁ Type} {lift₂ : Lift T₂ Type} where
      
        open Lifted lift₁ using () renaming (_↑✶_ to _↑✶₁_; _/✶_ to _/✶₁_)
        open Lifted lift₂ using () renaming (_↑✶_ to _↑✶₂_; _/✶_ to _/✶₂_)

        /✶-↑✶ : ∀ {m n} (σs₁ : Subs T₁ m n) (σs₂ : Subs T₂ m n) → 
                          (∀ k x → tvar x /✶₁ σs₁ ↑✶₁ k ≡ tvar x /✶₂ σs₂ ↑✶₂ k) → 
                          ∀ k t → t /✶₁ σs₁ ↑✶₁ k ≡ t /✶₂ σs₂ ↑✶₂ k
        /✶-↑✶ ρs₁ ρs₂ hyp k (tvar x) = hyp k x
        /✶-↑✶ ρs₁ ρs₂ hyp k (a →' b) = begin
            (a →' b) /✶₁ ρs₁ ↑✶₁ k
          ≡⟨ TypeApp.→'-/✶-↑✶ _ k ρs₁ ⟩
            (a /✶₁ ρs₁ ↑✶₁ k) →' (b /✶₁ ρs₁ ↑✶₁ k)
          ≡⟨ cong₂ _→'_ (/✶-↑✶ ρs₁ ρs₂ hyp k a) (/✶-↑✶ ρs₁ ρs₂ hyp k b) ⟩
            (a /✶₂ ρs₂ ↑✶₂ k) →' (b /✶₂ ρs₂ ↑✶₂ k)
          ≡⟨ sym (TypeApp.→'-/✶-↑✶ _ k ρs₂) ⟩
            (a →' b) /✶₂ ρs₂ ↑✶₂ k
          ∎
        /✶-↑✶ ρs₁ ρs₂ hyp k (∀' a) = begin
          (∀' a) /✶₁ ρs₁ ↑✶₁ k        ≡⟨ TypeApp.∀'-/✶-↑✶ _ k ρs₁ ⟩
          ∀' (a /✶₁ ρs₁ ↑✶₁ (1 N+ k))  ≡⟨ cong ∀' (/✶-↑✶ ρs₁ ρs₂ hyp (1 N+ k) a) ⟩
          ∀' (a /✶₂ ρs₂ ↑✶₂ (1 N+ k))  ≡⟨ sym (TypeApp.∀'-/✶-↑✶ _ k ρs₂) ⟩
          (∀' a) /✶₂ ρs₂ ↑✶₂ k        ∎

  module tpl = TermLemmas typeLemmas

  -- The above lemma /✶-↑✶ specialized to single substitutions
  /-↑⋆ : ∀ {T₁ T₂} {lift₁ : Lift T₁ Type} {lift₂ : Lift T₂ Type} →
         let open Lifted lift₁ using () renaming (_↑⋆_ to _↑⋆₁_; _/_ to _/₁_)
             open Lifted lift₂ using () renaming (_↑⋆_ to _↑⋆₂_; _/_ to _/₂_)
         in
         ∀ {n k} (ρ₁ : Sub T₁ n k) (ρ₂ : Sub T₂ n k) →
         (∀ i x → tvar x /₁ ρ₁ ↑⋆₁ i ≡ tvar x /₂ ρ₂ ↑⋆₂ i) →
          ∀ i a → a /₁ ρ₁ ↑⋆₁ i ≡ a /₂ ρ₂ ↑⋆₂ i
  /-↑⋆ ρ₁ ρ₂ hyp i a = tpl./✶-↑✶ (ρ₁ ◅ ε) (ρ₂ ◅ ε) hyp i a

  postulate a/var-wk-↑/sub-0≡a : ∀ {ν} (a : Type (suc ν)) → 
               (a /Var (VarSubst.wk VarSubst.↑)) / (sub $ tvar zero) ≡ a
  {-a/var-wk-↑/sub-0≡a a = begin
    (a /Var (VarSubst.wk VarSubst.↑)) / (sub $ tvar zero) ≡⟨ {!!} ⟩
    (a /Var (zero ∷ (map suc VarSubst.wk))) / ((tvar zero) ∷ TypeSubst.id) ≡⟨ {!!} ⟩
    a ∎-}

  open AdditionalLemmas typeLemmas public
  open tpl public

open TypeSubst public using () renaming (_/_ to _tp/tp_; _[/_] to _tp[/tp_]; weaken to tp-weaken)
