module Implicits.Calculus.Substitutions.Lemmas (TC : Set) where

open import Prelude
open import Implicits.Calculus.Types TC 
open import Implicits.Calculus.Terms TC 
open import Implicits.Calculus.Substitutions TC 
open import Data.Fin.Substitution

module TypeLemmas where
  open import Data.Fin.Substitution.Lemmas
  open TypeSubst
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
        /✶-↑✶ ρs₁ ρs₂ hyp k (tc c) = begin
            (tc c) /✶₁ ρs₁ ↑✶₁ k
          ≡⟨ TypeApp.tc-/✶-↑✶ _ k ρs₁ ⟩
            (tc c)
          ≡⟨ sym $ TypeApp.tc-/✶-↑✶ _ k ρs₂ ⟩
            (tc c) /✶₂ ρs₂ ↑✶₂ k ∎
        /✶-↑✶ ρs₁ ρs₂ hyp k (a →' b) = begin
            (a →' b) /✶₁ ρs₁ ↑✶₁ k
          ≡⟨ TypeApp.→'-/✶-↑✶ _ k ρs₁ ⟩
            (a /✶₁ ρs₁ ↑✶₁ k) →' (b /✶₁ ρs₁ ↑✶₁ k)
          ≡⟨ cong₂ _→'_ (/✶-↑✶ ρs₁ ρs₂ hyp k a) (/✶-↑✶ ρs₁ ρs₂ hyp k b) ⟩
            (a /✶₂ ρs₂ ↑✶₂ k) →' (b /✶₂ ρs₂ ↑✶₂ k)
          ≡⟨ sym (TypeApp.→'-/✶-↑✶ _ k ρs₂) ⟩
            (a →' b) /✶₂ ρs₂ ↑✶₂ k
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
