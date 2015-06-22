module Implicits.Syntactical.Substitutions.Lemmas where

open import Prelude
open import Implicits.Syntactical.Types
open import Implicits.Syntactical.Terms
open import Implicits.Syntactical.Contexts
open import Implicits.Syntactical.Substitutions
open import Data.Fin.Substitution
open import Data.Vec.Properties
open import Extensions.Substitution
open import Extensions.Vec

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
        /✶-↑✶ ρs₁ ρs₂ hyp k (a →' b) = begin
            (a →' b) /✶₁ ρs₁ ↑✶₁ k
          ≡⟨ TypeApp.→'-/✶-↑✶ _ k ρs₁ ⟩
            (a /✶₁ ρs₁ ↑✶₁ k) →' (b /✶₁ ρs₁ ↑✶₁ k)
          ≡⟨ cong₂ _→'_ (/✶-↑✶ ρs₁ ρs₂ hyp k a) (/✶-↑✶ ρs₁ ρs₂ hyp k b) ⟩
            (a /✶₂ ρs₂ ↑✶₂ k) →' (b /✶₂ ρs₂ ↑✶₂ k)
          ≡⟨ sym (TypeApp.→'-/✶-↑✶ _ k ρs₂) ⟩
            (a →' b) /✶₂ ρs₂ ↑✶₂ k
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

  open AdditionalLemmas typeLemmas public

module PTypeLemmas where
  open PTypeSubst
  module Tp = TypeSubst
  open import Data.Fin.Substitution.Lemmas
  open import Data.Star using (Star; ε; _◅_)
  
  typeLemmas : TermLemmas PolyType
  typeLemmas = record { termSubst = PTypeSubst.typeSubst; app-var = refl ; /✶-↑✶ = Lemma./✶-↑✶ }
    where
      module Lemma {T₁ T₂} {lift₁ : Lift T₁ PolyType} {lift₂ : Lift T₂ PolyType} where
      
        open Lifted lift₁ using () renaming (_↑✶_ to _↑✶₁_; _/✶_ to _/✶₁_)
        open Lifted lift₂ using () renaming (_↑✶_ to _↑✶₂_; _/✶_ to _/✶₂_)

        postulate /✶-↑✶ : ∀ {m n} (σs₁ : Subs T₁ m n) (σs₂ : Subs T₂ m n) → 
                          (∀ k x → (mono $ tvar x) /✶₁ σs₁ ↑✶₁ k ≡ (mono $ tvar x) /✶₂ σs₂ ↑✶₂ k) → 
                          ∀ k t → t /✶₁ σs₁ ↑✶₁ k ≡ t /✶₂ σs₂ ↑✶₂ k

  open TermLemmas typeLemmas public hiding (var; weaken; _/_; _↑)

  open AdditionalLemmas typeLemmas

  mono⋆weaken : ∀ {ν} → _≗_ {A = Type ν} (mono ∘ Tp.weaken) (weaken ∘ mono)
  mono⋆weaken (tvar n) = refl
  mono⋆weaken (a →' b) = cong₂ _→ₚ_ (mono⋆weaken a) (mono⋆weaken b)

  /tp-↑⋆/map-mono-↑ : ∀ {ν μ} a (s : Sub Type ν μ) → a /tp (s Tp.↑) ≡ a / ((map mono s) ↑)
  /tp-↑⋆/map-mono-↑ a s = cong (λ u → a / ((mono $ tvar zero) ∷ u)) map-weaken⋆mono
    where
      map-weaken⋆mono = begin
        (map mono $ map Tp.weaken s) ≡⟨ sym $ map-∘ mono Tp.weaken s ⟩
        (map (mono ∘ Tp.weaken) s) ≡⟨ map-cong mono⋆weaken s ⟩
        (map (weaken ∘ mono) s) ≡⟨ map-∘ weaken mono s ⟩
        (map weaken $ map mono s) ∎

  /-map-mono⋆tp/tp : ∀ {ν μ} a (s : Sub Type ν μ) → mono a / (map mono s) ≡ mono (a tp/tp s)
  /-map-mono⋆tp/tp (tvar n) s = sym $ lookup⋆map s mono n
  /-map-mono⋆tp/tp (a →' b) s = cong₂ _→ₚ_ (/-map-mono⋆tp/tp a s) (/-map-mono⋆tp/tp b s)

  {-# NO_TERMINATION_CHECK #-}
  →ₚ/-distrib : ∀ {ν μ} (a b : PolyType ν) (s : Sub Type ν μ) →
                    (a →ₚ b) /tp s ≡ (a /tp s) →ₚ (b /tp s)
  →ₚ/-distrib (mono x) (mono y) s = refl
  →ₚ/-distrib (mono a') (∀' b) s = begin
      ∀' ((weaken a →ₚ b) / (s' ↑))
        ≡⟨ cong ∀' (sym $ /tp-↑⋆/map-mono-↑ (weaken a →ₚ b) s) ⟩
      ∀' ((weaken a →ₚ b) /tp (s Tp.↑))
        ≡⟨ cong ∀' ((→ₚ/-distrib (weaken a) b) (s Tp.↑)) ⟩
      ∀' (((weaken a) /tp (s Tp.↑)) →ₚ (b /tp (s Tp.↑)))
        ≡⟨ cong₂ (λ u v → ∀' (u →ₚ v)) (/tp-↑⋆/map-mono-↑ (weaken a) s) (/tp-↑⋆/map-mono-↑ b s) ⟩
      ∀' (((weaken a) / s' ↑) →ₚ (b / s' ↑))
        ≡⟨ cong (λ u → ∀' (u →ₚ (b / s' ↑))) (weaken⋆↑ a s') ⟩
      ∀' (weaken (mono a' / s') →ₚ (b / s' ↑))
        ≡⟨ cong (λ u → ∀' (weaken u →ₚ (b / s' ↑))) (/-map-mono⋆tp/tp a' s) ⟩
      (mono (a' tp/tp s)) →ₚ ∀' (b / s' ↑)
        ≡⟨ cong (λ u → (u →ₚ ∀' (b / s' ↑))) (sym $ /-map-mono⋆tp/tp a' s) ⟩
      (a / s') →ₚ ((∀' b) / s') ∎
    where
      a = mono a'
      s' = map mono s
  →ₚ/-distrib (∀' a) b s = begin
      ∀' ((a →ₚ (weaken b)) / (s' ↑))
        ≡⟨ cong ∀' (sym $ /tp-↑⋆/map-mono-↑ (a →ₚ (weaken b)) s) ⟩
      ∀' ((a →ₚ (weaken b)) /tp (s Tp.↑))
        ≡⟨ cong ∀' (→ₚ/-distrib a (weaken b) (s Tp.↑)) ⟩
      ∀' ((a /tp (s Tp.↑)) →ₚ ((weaken b) /tp (s Tp.↑)))
        ≡⟨ cong₂ (λ u v → ∀' (u →ₚ v)) (/tp-↑⋆/map-mono-↑ a s) (/tp-↑⋆/map-mono-↑ (weaken b) s) ⟩
      ∀' ((a / (s' ↑)) →ₚ ((weaken b) / (s' ↑)))
        ≡⟨ cong (λ u → ∀' ((a / (s' ↑)) →ₚ u)) (weaken⋆↑ b s') ⟩
      (∀' a / s') →ₚ (b / s') ∎
    where s' = map mono s

  {-
  -- the following strong version is much much more difficult (if at all prova/-map-mono⋆tp/tp)
  →ₚ/-distrib' : ∀ {ν μ} (a b : PolyType ν) (s : Sub PolyType ν μ) →
                 (a →ₚ b) / s ≡ (a / s) →ₚ (b / s)
  →ₚ/-distrib' (mono a) (mono b) s = refl
  →ₚ/-distrib' (mono a) (∀' b) s = begin
    (mono a →ₚ ∀' b) / s ≡⟨ refl ⟩
    (∀' ((weaken $ mono a) →ₚ b)) / s ≡⟨ {!!} ⟩
    ∀' (((weaken $ mono a) →ₚ b) / (s ↑)) ≡⟨ cong ∀' (→ₚ/-distrib' (weaken $ mono a) b (s ↑)) ⟩
    ∀' ((((weaken $ mono a) / (s ↑)) →ₚ (b / (s ↑))))
      ≡⟨ cong (λ u → ∀' (u →ₚ (b / s ↑))) (weaken⋆↑ (mono a) s) ⟩
    ∀' (((weaken (mono a / s)) →ₚ (b / (s ↑))))
      ≡⟨ {!!} ⟩
    (mono a / s) →ₚ (∀' b / s) ∎
  →ₚ/-distrib' (∀' a) b s = {!!}
  -}

module BindingLemmas where
  open BindingSubst 
  module pt = PTypeSubst

  totype⋆binding/ : ∀ {ν μ} (x : Binding ν) (σ : Sub Type ν μ) →
      (totype x) pt/tp σ ≡ totype (x / σ)
  totype⋆binding/ (val x) σ = refl
  totype⋆binding/ (rule a b) σ = PTypeLemmas.→ₚ/-distrib a b σ

open TypeSubst public using () 
  renaming (_/_ to _tp/tp_; _[/_] to _tp[/tp_])
open PTypeSubst public using ()
  renaming (_/_ to _ptp/tp_; _[/_] to _ptp[/tp_]; weaken to pt-weaken)
