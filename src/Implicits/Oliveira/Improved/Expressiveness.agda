open import Prelude hiding (id; Bool)

module Implicits.Oliveira.Improved.Expressiveness TC _tc≟_ where

open import Implicits.Oliveira.Types TC _tc≟_
open import Implicits.Oliveira.Terms TC _tc≟_
open import Implicits.Oliveira.Contexts TC _tc≟_
open import Implicits.Oliveira.WellTyped TC _tc≟_
open import Implicits.Oliveira.Substitutions TC _tc≟_
open import Extensions.ListFirst

open import Implicits.Oliveira.Ambiguous.Resolution TC _tc≟_ as A
open import Implicits.Oliveira.Deterministic.Resolution TC _tc≟_ as D
open import Implicits.Oliveira.Improved.Resolution TC _tc≟_ as I
  
module Lemmas₀ where
  mutual
    lemma₀ : ∀ {ν n} {K : Ktx ν n} {a r} → K D.⊢ r ↓ a → K I.⊢ r ↓ a
    lemma₀ (i-simp a) = i-simp a
    lemma₀ (i-iabs x x₁) = i-iabs (≥-deterministic x) (lemma₀ x₁)
    lemma₀ (i-tabs b x) = i-tabs b (lemma₀ x)

    lemma₁ : ∀ {ν n} {K : Ktx ν n} {Δ : ICtx ν} {a r} → Δ D.⟨ a ⟩= r → K D.⊢ r ↓ a → 
            first r ∈ Δ ⇔ (λ r' → K I.⊢ r' ↓ a)
    lemma₁ (l-head x Δ) y = here (lemma₀ y) Δ
    lemma₁ (l-tail {r = r} x x₁) y = there r (lemma₂ x) (lemma₁ x₁ y)
      where
        lemma₃ : ∀ {ν n} {K : Ktx ν n} {a r} → K I.⊢ r ↓ a → r ◁ a
        lemma₃ (i-simp _) = m-simp
        lemma₃ (i-iabs _ r2↓a) = m-iabs (lemma₃ r2↓a)
        lemma₃ (i-tabs _ r↓a) = m-tabs (lemma₃ r↓a)

        lemma₂ : ∀ {ν n} {K : Ktx ν n} {a r} → ¬ r ◁ a → ¬ K I.⊢ r ↓ a
        lemma₂ ¬a◁a (i-simp a) = ¬a◁a m-simp
        lemma₂ ¬r◁a (i-iabs ⊢ᵣr₁ r₂↓a) = ¬r◁a (m-iabs (lemma₃ r₂↓a))
        lemma₂ ¬r◁a (i-tabs b r[/]↓a) = ¬r◁a (m-tabs (lemma₃ r[/]↓a))

    ≥-deterministic : ∀ {ν n} {K : Ktx ν n} {a} → K D.⊢ᵣ a → K I.⊢ᵣ a
    ≥-deterministic (r-simp {τ = a} Δ⟨a⟩=r r↓a) = r-simp (lemma₁ Δ⟨a⟩=r r↓a)
    ≥-deterministic (r-iabs ρ₁ x) = r-iabs ρ₁ (≥-deterministic x)
    ≥-deterministic (r-tabs x) = r-tabs (≥-deterministic x)

module Lemmas₁ where
 mutual
    lemma₀ : ∀ {ν n} {K : Ktx ν n} {r a} → K I.⊢ r ↓ a → K A.⊢ᵣ r → K A.⊢ᵣ simpl a
    lemma₀ (i-simp a) x = x
    lemma₀ (i-iabs ⊢r1 r2↓a) x = lemma₀ r2↓a (r-iapp x (soundness ⊢r1))
    lemma₀ (i-tabs b r[/b]↓a) x = lemma₀ r[/b]↓a (r-tapp b x)

    {-# NO_TERMINATION_CHECK #-}
    soundness : ∀ {ν n} {K : Ktx ν n} {a} → K I.⊢ᵣ a → K A.⊢ᵣ a
    soundness (r-simp x) with first⟶∈ x
    soundness {ν} {n} {proj₁ , proj₂} (r-simp x) | proj₃ , proj₄ = lemma₀ proj₄ (r-ivar proj₃)
    soundness (r-iabs ρ₁ x) = r-iabs (soundness x)
    soundness (r-tabs x) = r-tabs (soundness x)

