open import Prelude renaming (lift to finlift) hiding (id; subst)

module Implicits.Substitutions.Lemmas.Type (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Implicits.Syntax.Type TC _tc≟_
open import Implicits.Substitutions TC _tc≟_
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas 
open import Data.Vec.Properties
open import Extensions.Substitution
open import Data.Star using (Star; ε; _◅_)

typeLemmas : TermLemmas Type
typeLemmas = record { termSubst = TypeSubst.typeSubst; app-var = refl ; /✶-↑✶ = Lemma./✶-↑✶ }
  where
    open TypeSubst
    module Lemma {T₁ T₂} {lift₁ : Lift T₁ Type} {lift₂ : Lift T₂ Type} where

      open Lifted lift₁ using () renaming (_↑✶_ to _↑✶₁_; _/✶_ to _/✶₁_)
      open Lifted lift₂ using () renaming (_↑✶_ to _↑✶₂_; _/✶_ to _/✶₂_)

      /✶-↑✶ : ∀ {m n} (σs₁ : Subs T₁ m n) (σs₂ : Subs T₂ m n) → 
                          (∀ k x → (simpl (tvar x)) /✶₁ σs₁ ↑✶₁ k ≡ (simpl (tvar x)) /✶₂ σs₂ ↑✶₂ k) → 
                          ∀ k t → t /✶₁ σs₁ ↑✶₁ k ≡ t /✶₂ σs₂ ↑✶₂ k
      /✶-↑✶ ρs₁ ρs₂ hyp k (simpl (tvar x)) = hyp k x
      /✶-↑✶ ρs₁ ρs₂ hyp k (simpl (tc c)) = begin
          (simpl $ tc c) /✶₁ ρs₁ ↑✶₁ k
          ≡⟨ TypeApp.tc-/✶-↑✶ _ k ρs₁ ⟩
          (simpl $ tc c)
          ≡⟨ sym $ TypeApp.tc-/✶-↑✶ _ k ρs₂ ⟩
          (simpl $ tc c) /✶₂ ρs₂ ↑✶₂ k ∎
      /✶-↑✶ ρs₁ ρs₂ hyp k (simpl (a →' b)) = begin
          (simpl $ a →' b) /✶₁ ρs₁ ↑✶₁ k
          ≡⟨ TypeApp.→'-/✶-↑✶ _ k ρs₁ ⟩
          simpl ((a /✶₁ ρs₁ ↑✶₁ k) →' (b /✶₁ ρs₁ ↑✶₁ k))
          ≡⟨ cong₂ (λ a b → simpl (a →' b)) (/✶-↑✶ ρs₁ ρs₂ hyp k a) (/✶-↑✶ ρs₁ ρs₂ hyp k b) ⟩
          simpl ((a /✶₂ ρs₂ ↑✶₂ k) →' (b /✶₂ ρs₂ ↑✶₂ k))
          ≡⟨ sym (TypeApp.→'-/✶-↑✶ _ k ρs₂) ⟩
          (simpl $ a →' b) /✶₂ ρs₂ ↑✶₂ k
          ∎
      /✶-↑✶ ρs₁ ρs₂ hyp k (a ⇒ b) = begin
          (a ⇒ b) /✶₁ ρs₁ ↑✶₁ k
          ≡⟨ TypeApp.⇒-/✶-↑✶ _ k ρs₁ ⟩ -- 
          (a /✶₁ ρs₁ ↑✶₁ k) ⇒ (b /✶₁ ρs₁ ↑✶₁ k)
          ≡⟨ cong₂ _⇒_ (/✶-↑✶ ρs₁ ρs₂ hyp k a) (/✶-↑✶ ρs₁ ρs₂ hyp k b) ⟩
          (a /✶₂ ρs₂ ↑✶₂ k) ⇒ (b /✶₂ ρs₂ ↑✶₂ k)
          ≡⟨ sym (TypeApp.⇒-/✶-↑✶ _ k ρs₂) ⟩
          (a ⇒ b) /✶₂ ρs₂ ↑✶₂ k
          ∎
      /✶-↑✶ ρs₁ ρs₂ hyp k (∀' a) = begin
          (∀' a) /✶₁ ρs₁ ↑✶₁ k
          ≡⟨ TypeApp.∀'-/✶-↑✶ _ k ρs₁ ⟩
          ∀' (a /✶₁ ρs₁ ↑✶₁ (suc k))
          ≡⟨ cong ∀' (/✶-↑✶ ρs₁ ρs₂ hyp (suc k) a) ⟩
          ∀' (a /✶₂ ρs₂ ↑✶₂ (suc k))
          ≡⟨ sym (TypeApp.∀'-/✶-↑✶ _ k ρs₂) ⟩
          (∀' a) /✶₂ ρs₂ ↑✶₂ k
          ∎

open TermLemmas typeLemmas public hiding (var; id)
open AdditionalLemmas typeLemmas public
open TypeSubst using (module Lifted) 

-- The above lemma /✶-↑✶ specialized to single substitutions
/-↑⋆ : ∀ {T₁ T₂} {lift₁ : Lift T₁ Type} {lift₂ : Lift T₂ Type} →
    let open Lifted lift₁ using () renaming (_↑⋆_ to _↑⋆₁_; _/_ to _/₁_)
        open Lifted lift₂ using () renaming (_↑⋆_ to _↑⋆₂_; _/_ to _/₂_)
    in
    ∀ {n k} (ρ₁ : Sub T₁ n k) (ρ₂ : Sub T₂ n k) →
    (∀ i x → (simpl (tvar x)) /₁ ρ₁ ↑⋆₁ i ≡ (simpl (tvar x)) /₂ ρ₂ ↑⋆₂ i) →
        ∀ i a → a /₁ ρ₁ ↑⋆₁ i ≡ a /₂ ρ₂ ↑⋆₂ i
/-↑⋆ ρ₁ ρ₂ hyp i a = /✶-↑✶ (ρ₁ ◅ ε) (ρ₂ ◅ ε) hyp i a

-- weakening a simple type gives a simple type
simpl-wk : ∀ {ν} k (τ : SimpleType (k N+ ν)) → ∃ λ τ' → (simpl τ) / wk ↑⋆ k ≡ simpl τ'
simpl-wk k (tc x) = , refl
simpl-wk k (tvar n) = , var-/-wk-↑⋆ k n
simpl-wk k (x →' x₁) = , refl

-- ◁-wk : ∀ {ν} (a : Type ν) → proj₂ ((weaken a) ◁) ≡ weaken (proj₂ (a ◁))
-- ◁-wk a = ?
