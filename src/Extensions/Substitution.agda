open import Prelude
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas

module Extensions.Substitution where
  
  module AdditionalLemmas {T} (lemmas : TermLemmas T) where

    open TermLemmas lemmas

    -- Weakening commutes with single-variable substitution
    weaken-sub : ∀ {n} (a : T (1 N+ n)) (b : T n) →
                 weaken (a / sub b) ≡ a / wk ↑ / sub (weaken b)
    weaken-sub a b = begin
      weaken (a / sub b)        ≡⟨ sym (/-wk′ (a / sub b)) ⟩
      a / sub b / wk            ≡⟨ sub-commutes a ⟩
      a / wk ↑ / sub (b / wk)   ≡⟨ cong (λ c → a / wk ↑ / sub c) (/-wk′ b) ⟩
      a / wk ↑ / sub (weaken b) ∎
      where /-wk′ : ∀ {n} (a : T n) → a / wk ≡ weaken a
            /-wk′ a = /-wk {t = a}

    -- Weakening commutes with reverse composition of substitutions.
    map-weaken-⊙ : ∀ {m n k} (σ₁ : Sub T m n) (σ₂ : Sub T n k) →
                   map weaken (σ₁ ⊙ σ₂) ≡ (map weaken σ₁) ⊙ (σ₂ ↑)
    map-weaken-⊙ σ₁ σ₂ = begin
      map weaken (σ₁ ⊙ σ₂)     ≡⟨ map-weaken ⟩
      (σ₁ ⊙ σ₂) ⊙ wk           ≡⟨ sym ⊙-assoc ⟩
      σ₁ ⊙ (σ₂ ⊙ wk)           ≡⟨ cong (λ σ₂ → σ₁ ⊙ σ₂) ⊙-wk ⟩
      σ₁ ⊙ (wk ⊙ (σ₂ ↑))       ≡⟨ ⊙-assoc ⟩
      (σ₁ ⊙ wk) ⊙ (σ₂ ↑)       ≡⟨ cong (λ σ₁ → σ₁ ⊙ (σ₂ ↑)) (sym map-weaken) ⟩
      (map weaken σ₁) ⊙ (σ₂ ↑) ∎

    weaken⋆↑ : ∀ {ν μ} (x : T ν) (s : Sub T ν μ) → (weaken x) / (s ↑) ≡ weaken (x / s)
    weaken⋆↑ x s = begin
      (weaken x) / (s ↑) ≡⟨ cong (λ u → u / (s ↑)) (sym /-wk) ⟩
      x / wk / (s ↑) ≡⟨ sym (/-⊙ x) ⟩
      x / (wk ⊙ (s ↑)) ≡⟨ cong (_/_ x) (sym ⊙-wk) ⟩
      x / (s ⊙ wk) ≡⟨ /-⊙ x ⟩
      x / s / wk ≡⟨ /-wk ⟩
      weaken (x / s) ∎

    weaken-sub-vanishes : ∀ {ν} {a b : T ν} → (weaken a) / (sub b) ≡ a
    weaken-sub-vanishes {ν} {a} {b} = begin
      (weaken a) / (sub b) ≡⟨ cong (flip _/_ (sub b)) (sym $ /-wk {t = a}) ⟩
      a / wk / (sub b) ≡⟨ wk-sub-vanishes a ⟩
      a ∎

    postulate a/wk↑/sub0≡a : ∀ {ν} (a : T (suc ν)) → a / wk ↑ / (sub $ var zero) ≡ a
    {-a/var-wk-↑/sub-0≡a a = begin
        (a /Var (VarSubst.wk VarSubst.↑)) / (sub $ tvar zero) ≡⟨ {!!} ⟩
        (a /Var (zero ∷ (map suc VarSubst.wk))) / ((tvar zero) ∷ TypeSubst.id) ≡⟨ {!!} ⟩
        a ∎-}
