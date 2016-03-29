open import Prelude hiding (id; Bool)

module Implicits.Resolution.Undecidable.Expressiveness where

open import Implicits.Syntax
open import Implicits.Substitutions
open import Extensions.ListFirst

open import Implicits.Resolution.Ambiguous.Resolution as A
open import Implicits.Resolution.Deterministic.Resolution as D
open import Implicits.Resolution.Undecidable.Resolution as I
  
mutual
  ↓-sound : ∀ {ν} {Δ : ICtx ν} {a r} → Δ D.⊢ r ↓ a → Δ I.⊢ r ↓ a
  ↓-sound (i-simp a) = i-simp a
  ↓-sound (i-iabs x x₁) = i-iabs (≥-deterministic x) (↓-sound x₁)
  ↓-sound (i-tabs b x) = i-tabs b (↓-sound x)

  Δ⟨τ⟩-sound : ∀ {ν} {Δ Δ' : ICtx ν} {a r} → Δ D.⟨ a ⟩= r → Δ' D.⊢ r ↓ a → 
              first r ∈ Δ ⇔ (λ r' → Δ' I.⊢ r' ↓ a)
  Δ⟨τ⟩-sound (here p v) y = here (↓-sound y) v
  Δ⟨τ⟩-sound (there x ¬x◁τ p) y = there x (¬◁-¬↓ ¬x◁τ) (Δ⟨τ⟩-sound p y)
    where
      ↓-◁ : ∀ {ν} {Δ : ICtx ν} {a r} → Δ I.⊢ r ↓ a → r ◁ a
      ↓-◁ (i-simp _) = m-simp
      ↓-◁ (i-iabs _ r2↓a) = m-iabs (↓-◁ r2↓a)
      ↓-◁ (i-tabs b r↓a) = m-tabs b (↓-◁ r↓a)

      ¬◁-¬↓ : ∀ {ν} {Δ : ICtx ν} {a r} → ¬ r ◁ a → ¬ Δ I.⊢ r ↓ a
      ¬◁-¬↓ ¬a◁a (i-simp a) = ¬a◁a m-simp
      ¬◁-¬↓ ¬r◁a (i-iabs ⊢ᵣr₁ r₂↓a) = ¬r◁a (m-iabs (↓-◁ r₂↓a))
      ¬◁-¬↓ ¬r◁a (i-tabs b r[/]↓a) = ¬r◁a (m-tabs b (↓-◁ r[/]↓a))

  ≥-deterministic : ∀ {ν} {Δ : ICtx ν} {a} → Δ D.⊢ᵣ a → Δ I.⊢ᵣ a
  ≥-deterministic (r-simp {τ = a} Δ⟨a⟩=r r↓a) = r-simp (Δ⟨τ⟩-sound Δ⟨a⟩=r r↓a)
  ≥-deterministic (r-iabs ρ₁ x) = r-iabs ρ₁ (≥-deterministic x)
  ≥-deterministic (r-tabs x) = r-tabs (≥-deterministic x)
