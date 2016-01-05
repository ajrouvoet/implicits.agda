open import Prelude hiding (id; Bool)

module Implicits.Resolution.Undecidable.Expressiveness TC _tc≟_ where

open import Implicits.Syntax TC _tc≟_
open import Implicits.Substitutions TC _tc≟_
open import Extensions.ListFirst

open import Implicits.Resolution.Ambiguous.Resolution TC _tc≟_ as A
open import Implicits.Resolution.Deterministic.Resolution TC _tc≟_ as D
open import Implicits.Resolution.Undecidable.Resolution TC _tc≟_ as I
  
mutual
  ↓-sound : ∀ {ν} {Δ : ICtx ν} {a r} → Δ D.⊢ r ↓ a → Δ I.⊢ r ↓ a
  ↓-sound (i-simp a) = i-simp a
  ↓-sound (i-iabs x x₁) = i-iabs (≥-deterministic x) (↓-sound x₁)
  ↓-sound (i-tabs b x) = i-tabs b (↓-sound x)

  Δ⟨τ⟩-sound : ∀ {ν} {Δ : ICtx ν} {a r} →
              Δ D.⟨ a ⟩= r → Δ D.⊢ r ↓ a → 
              first r ∈ Δ ⇔ (λ r' → Δ I.⊢ r' ↓ a)
  Δ⟨τ⟩-sound x y = lem₁ x y
    where
      lem₃ : ∀ {ν} {Δ : ICtx ν} {a r} → Δ I.⊢ r ↓ a → r ◁ a
      lem₃ (i-simp _) = m-simp
      lem₃ (i-iabs _ r2↓a) = m-iabs (lem₃ r2↓a)
      lem₃ (i-tabs _ r↓a) = m-tabs (lem₃ r↓a)

      lem₂ : ∀ {ν} {Δ : ICtx ν} {a r} → ¬ r ◁ a → ¬ Δ I.⊢ r ↓ a
      lem₂ ¬a◁a (i-simp a) = ¬a◁a m-simp
      lem₂ ¬r◁a (i-iabs ⊢ᵣr₁ r₂↓a) = ¬r◁a (m-iabs (lem₃ r₂↓a))
      lem₂ ¬r◁a (i-tabs b r[/]↓a) = ¬r◁a (m-tabs (lem₃ r[/]↓a))

      lem₁ : ∀ {ν} {Δ Δ' : ICtx ν} {a r} → Δ D.⟨ a ⟩= r → Δ' D.⊢ r ↓ a → 
              first r ∈ Δ ⇔ (λ r' → Δ' I.⊢ r' ↓ a)
      lem₁ (l-head x Δ) y = here (↓-sound y) Δ
      lem₁ (l-tail {r = r} x x₁) y = there r (lem₂ x) (lem₁ x₁ y)

  ≥-deterministic : ∀ {ν} {Δ : ICtx ν} {a} → Δ D.⊢ᵣ a → Δ I.⊢ᵣ a
  ≥-deterministic (r-simp {τ = a} Δ⟨a⟩=r r↓a) = r-simp (Δ⟨τ⟩-sound Δ⟨a⟩=r r↓a)
  ≥-deterministic (r-iabs ρ₁ x) = r-iabs ρ₁ (≥-deterministic x)
  ≥-deterministic (r-tabs x) = r-tabs (≥-deterministic x)
