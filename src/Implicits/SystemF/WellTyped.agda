module Implicits.SystemF.WellTyped where

open import Prelude
open import Data.Fin.Substitution
open import Implicits.SystemF.Types public
open import Implicits.SystemF.Terms public
open import Implicits.SystemF.Contexts public
open import Data.Vec.Properties

infix 4 _⊢_∈_

data _⊢_∈_ {ν n} (Γ : Ctx ν n) : Term ν n → Type ν → Set where
  var : (x : Fin n) → Γ ⊢ var x ∈ lookup x Γ
  Λ   : ∀ {t a} → (ctx-weaken Γ) ⊢ t ∈ a → Γ ⊢ Λ t ∈ ∀' a
  λ'  : ∀ {t b} → (a : Type ν) → a ∷ Γ ⊢ t ∈ b → Γ ⊢ λ' a t ∈ a →' b
  _[_] : ∀ {t a} → Γ ⊢ t ∈ ∀' a → (b : Type ν) → Γ ⊢ t [ b ] ∈ a tp[/tp b ]
  _·_  : ∀ {f t a b} → Γ ⊢ f ∈ (a →' b) → Γ ⊢ t ∈ a → Γ ⊢ f · t ∈ b
  
_⊢_∉_ : ∀ {ν n} → (Γ : Ctx ν n) → Term ν n → Type ν → Set
_⊢_∉_ Γ t τ = ¬ Γ ⊢ t ∈ τ
  
⊢erase : ∀ {ν n} {Γ : Ctx ν n} {t τ} → Γ ⊢ t ∈ τ → Term ν n
⊢erase (var x) = var x
⊢erase (Λ {t} x) = Λ t
⊢erase (λ' {t} a x) = λ' a t
⊢erase (_[_] {t} x b) = t
⊢erase (_·_ {f} x x₁) = f

⊢f·a-inversion : ∀ {ν n f t b} {Γ : Ctx ν n} → Γ ⊢ f · t ∈ b → 
                 ∃ λ a → Γ ⊢ f ∈ a →' b × Γ ⊢ t ∈ a
⊢f·a-inversion (_·_ f∈a→b t∈a) = , (f∈a→b , t∈a)

⊢tc[a]-inversion : ∀ {ν n tc a' b} {Γ : Ctx ν n} → Γ ⊢ tc [ b ] ∈ a' → ∃ λ a → Γ ⊢ tc ∈ ∀' a
⊢tc[a]-inversion (_[_] tc∈∀'a b) = , tc∈∀'a

unique-type : ∀ {ν n} {Γ : Ctx ν n} {t τ τ'} → Γ ⊢ t ∈ τ → Γ ⊢ t ∈ τ' → τ ≡ τ'
unique-type (var x) (var .x) = refl
unique-type (Λ l) (Λ r) = cong ∀' (unique-type l r)
unique-type (λ' a l) (λ' .a r) = cong (λ b → a →' b) (unique-type l r)
unique-type (l [ b ]) (r [ .b ]) = cong (λ{ (∀' fa) → fa tp[/tp b ]; a → a}) (unique-type l r)
unique-type (f · e) (f' · e') = cong (λ{ (a →' b) → b; a → a }) (unique-type f f')

unique-type′ : ∀ {ν n} {Γ : Ctx ν n} {t τ τ'} → Γ ⊢ t ∈ τ → τ ≢ τ' → Γ ⊢ t ∉ τ'
unique-type′ ⊢t∈τ neq ⊢t∈τ' = neq $ unique-type ⊢t∈τ ⊢t∈τ'

module WellTypedLemmas where
  postulate ⊢/-preserves : ∀ {ν μ n} {Γ : Ctx ν n} {t a} → Γ ⊢ t ∈ a → (s : Sub Type ν μ) → Γ ctx/ s ⊢ t tm/tp s ∈ a tp/tp s
  
  ctx-weaken-sub-vanishes : ∀ {ν n} {Γ : Ctx ν n} {a} → (ctx-weaken Γ) ctx/ (TypeSubst.sub a) ≡ Γ
  ctx-weaken-sub-vanishes {Γ = Γ} {a} = begin
    (Γ ctx/ TypeSubst.wk) ctx/ (TypeSubst.sub a) 
      ≡⟨ sym $ map-∘ (λ s → s tp/tp TypeSubst.sub a) (λ s → s tp/tp TypeSubst.wk) Γ ⟩
    (map (λ s → s tp/tp TypeSubst.wk tp/tp (TypeSubst.sub a)) Γ) 
      ≡⟨ map-cong (TypeLemmas.wk-sub-vanishes) Γ ⟩
    (map (λ s → s) Γ) ≡⟨ map-id Γ ⟩
    Γ ∎

  tm[/tp]-preserves : ∀ {ν n} {Γ : Ctx ν n} {t τ} → Γ ⊢ Λ t ∈ ∀' τ → ∀ a → Γ ⊢ (t tm[/tp a ]) ∈ τ tp[/tp a ]
  tm[/tp]-preserves {Γ = Γ} {t} {τ} (Λ p) a = 
    ctx-subst ctx-weaken-sub-vanishes (⊢/-preserves p (TypeSubst.sub a))
    where
      ctx-subst = subst (λ c → c ⊢ t tm[/tp a ] ∈ τ tp[/tp a ])

  postulate tm[/tm]-preserves : ∀ {ν n} {Γ : Ctx ν n} {t u a b} → 
                      b ∷ Γ ⊢ t ∈ a → Γ ⊢ u ∈ b → Γ ⊢ (t tm[/tm u ]) ∈ a
  -- tm[/tm]-preserves {Γ = Γ} {t} {u} {a} {b} t∈a u∈b = {!!}

  postulate ⊢weaken-preserves : ∀ {ν n} {K : Ctx ν n} {t a} → K ⊢ t ∈ a → ctx-weaken K ⊢ tm-weaken t ∈ tp-weaken a
