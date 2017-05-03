module Extensions.Substitution where

open import Prelude hiding (id)

open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Vec.Properties
open import Data.Vec
open import Function hiding (id)

module AdditionalLemmas {T} (lemmas : TermLemmas T) where

  open TermLemmas lemmas
  module Var = VarSubst

  -- Weakening commutes with single-variable substitution
  weaken-sub : ∀ {n} (a : T (1 + n)) (b : T n) →
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

  -- make /Var usable from lemmas
  open TermSubst termSubst using (_/Var_) public

  private
    var⋆weaken : ∀ {n} → _≗_ {A = Fin n} (var ∘ suc) (weaken ∘ var)
    var⋆weaken n = begin 
      var (suc n) ≡⟨ sym $ lookup-wk n ⟩
      lookup n wk ≡⟨ sym $ var-/ ⟩
      (var n) / wk ≡⟨ /-wk ⟩
      weaken (var n) ∎

    map-var⋆weaken : ∀ {n m} {v : Vec (Fin n) m} → map var (map suc v) ≡ map weaken (map var v)
    map-var⋆weaken {v = v} = begin
      map var (map suc v) ≡⟨ sym $ map-∘ var suc v ⟩
      map (var ∘ suc) v ≡⟨ map-cong var⋆weaken v ⟩
      map (weaken ∘ var) v ≡⟨ map-∘ weaken var v ⟩
      map weaken (map var v) ∎

  map-var-varid≡id : ∀ {n} → map var (Var.id {n}) ≡ id {n}
  map-var-varid≡id {zero} = refl
  map-var-varid≡id {suc n} = begin
    var zero ∷ (map var $ map suc Var.id)
      ≡⟨ cong (_∷_ (var zero)) map-var⋆weaken ⟩
    var zero ∷ (map weaken $ map var Var.id)
      ≡⟨ cong (λ u → var zero ∷ (map weaken u)) map-var-varid≡id ⟩
    id ↑ ∎

  map-var-varwk≡wk : ∀ {n} → map var (Var.wk {n}) ≡ wk {n}
  map-var-varwk≡wk {zero} = refl
  map-var-varwk≡wk {suc n} = begin
    map var (map suc Var.id) ≡⟨ map-var⋆weaken ⟩ 
    map weaken (map var Var.id) ≡⟨ cong (map weaken) map-var-varid≡id ⟩
    wk ∎ 

  map-var-↑ : ∀ {n m} {s : Vec (Fin n) m} {s'} → map var s ≡ s' → map var (s Var.↑) ≡ s' ↑
  map-var-↑ {s = s} {s' = s'} eq = begin
    var zero ∷ (map var $ map suc s)
      ≡⟨ cong (_∷_ $ var zero) map-var⋆weaken ⟩
    var zero ∷ (map weaken $ map var s)
      ≡⟨ cong (λ u → var zero ∷ (map weaken u)) eq ⟩
    s' ↑ ∎

  a/wk↑/sub0≡a : ∀ {ν} (a : T (suc ν)) → a / wk ↑ / (sub $ var zero) ≡ a
  a/wk↑/sub0≡a a = begin
    a / wk ↑ / (sub $ var zero)
      ≡⟨ sym $ /-⊙ a ⟩
    a / (var zero / (sub $ var zero) ∷ map /-var-zero (map weaken wk))
      ≡⟨ cong (λ u → a / (u ∷ map /-var-zero (map weaken wk))) var-/ ⟩
    a / (var zero ∷ map /-var-zero (map weaken wk))
      ≡⟨ cong' (sym $ map-∘ /-var-zero weaken wk) ⟩
    a / (var zero ∷ map (λ t → (weaken t) / (sub $ var zero)) wk)
      ≡⟨ cong' (map-cong (λ t → weaken-sub-vanishes) wk) ⟩
    a / (var zero ∷ map Prelude.id wk)
      ≡⟨ cong' (map-id wk) ⟩
    a / ((var zero ∷ wk))
      ≡⟨ id-vanishes a ⟩
    a ∎
    where
      /-var-zero = (λ t → t / (sub $ var zero))
      cong' : ∀ {x y} → x ≡ y → a / (var zero ∷ x) ≡ a / (var zero ∷ y)
      cong' = λ rest → cong (λ u → a / (var zero ∷ u)) rest 
