module SystemF.WellTyped where

open import Prelude hiding (id; erase)

open import SystemF.Syntax public
open import SystemF.Substitutions
open import Data.Vec hiding ([_])
open import Data.Vec.Properties
open import Data.Product

infix 4 _⊢_∈_
data _⊢_∈_ {ν n} (Γ : Ctx ν n) : Term ν n → Type ν → Set where
  var : (x : Fin n) → Γ ⊢ var x ∈ lookup x Γ
  Λ   : ∀ {t a} → (ctx-weaken Γ) ⊢ t ∈ a → Γ ⊢ Λ t ∈ ∀' a
  λ'  : ∀ {t b} → (a : Type ν) → a ∷ Γ ⊢ t ∈ b → Γ ⊢ λ' a t ∈ a →' b
  _[_] : ∀ {t a} → Γ ⊢ t ∈ ∀' a → (b : Type ν) → Γ ⊢ t [ b ] ∈ a tp[/tp b ]
  _·_  : ∀ {f t a b} → Γ ⊢ f ∈ (a →' b) → Γ ⊢ t ∈ a → Γ ⊢ f · t ∈ b

_⊢_∉_ : ∀ {ν n} → (Γ : Ctx ν n) → Term ν n → Type ν → Set
_⊢_∉_ Γ t τ = ¬ Γ ⊢ t ∈ τ

erase : ∀ {ν n} {Γ : Ctx ν n} {t τ} → Γ ⊢ t ∈ τ → Term ν n
erase (var x) = var x
erase (Λ {t} x) = Λ t
erase (λ' {t} a x) = λ' a t
erase (_[_] {t} x b) = t
erase (_·_ {f} x x₁) = f

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

-- Collections of typing derivations for well-typed terms.
data _⊢ⁿ_∈_ {m n} (Γ : Ctx n m) :
  ∀ {k} → Vec (Term n m) k → Vec (Type n) k → Set where
    []  : Γ ⊢ⁿ [] ∈ []
    _∷_ : ∀ {t a k} {ts : Vec (Term n m) k} {as : Vec (Type n) k} →
          Γ ⊢ t ∈ a → Γ ⊢ⁿ ts ∈ as → Γ ⊢ⁿ t ∷ ts ∈ (a ∷ as)

-- Lookup a well-typed term in a collection thereof.
lookup-⊢ : ∀ {m n k} {Γ : Ctx n m} {ts : Vec (Term n m) k}
             {as : Vec (Type n) k} →
           (x : Fin k) → Γ ⊢ⁿ ts ∈ as → Γ ⊢ lookup x ts ∈ lookup x as
lookup-⊢ zero    (⊢t ∷ ⊢ts) = ⊢t
lookup-⊢ (suc x) (⊢t ∷ ⊢ts) = lookup-⊢ x ⊢ts
