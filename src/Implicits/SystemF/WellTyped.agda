module Implicits.SystemF.WellTyped where

open import Prelude
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Implicits.SystemF.Types public renaming (module TypeSubst to TS)
open import Implicits.SystemF.Terms public renaming (module TermTermSubst to TmTmS)
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

private
  ⊢subst : ∀ {m n} {Γ₁ Γ₂ : Ctx n m} {t₁ t₂ : Term n m} {a₁ a₂ : Type n} →
    Γ₁ ≡ Γ₂ → t₁ ≡ t₂ → a₁ ≡ a₂ → Γ₁ ⊢ t₁ ∈ a₁ → Γ₂ ⊢ t₂ ∈ a₂
  ⊢subst refl refl refl hyp = hyp

  ⊢substCtx : ∀ {m n} {Γ₁ Γ₂ : Ctx n m} {t : Term n m} {a : Type n} →
    Γ₁ ≡ Γ₂ → Γ₁ ⊢ t ∈ a → Γ₂ ⊢ t ∈ a
  ⊢substCtx refl hyp = hyp

  ⊢substTp : ∀ {m n} {Γ : Ctx n m} {t : Term n m} {a₁ a₂ : Type n} →
    a₁ ≡ a₂ → Γ ⊢ t ∈ a₁ → Γ ⊢ t ∈ a₂
  ⊢substTp refl hyp = hyp 

module WtTypeSubst where
  open TypeLemmas hiding (_/_; var; weaken)
  private
    module Tp = TypeLemmas
    module Tm = TermTypeLemmas
    module C  = CtxSubst

  infixl 8 _/_

  -- Type substitutions lifted to well-typed terms
  _/_ : ∀ {m n k} {Γ : Ctx n m} {t : Term n m} {a : Type n} →
        Γ ⊢ t ∈ a → (σ : Sub Type n k) → Γ C./ σ ⊢ t Tm./ σ ∈ a Tp./ σ
  var x             / σ = ⊢substTp (lookup-⊙ x) (var x)
  _/_ {Γ = Γ} (Λ ⊢t)  σ = Λ (⊢substCtx eq (⊢t / σ ↑))
    where
      eq : (ctx-weaken Γ) C./ (σ Tp.↑) ≡ ctx-weaken (Γ C./ σ)
      eq = begin 
        (map (λ s → s tp/tp TS.wk) Γ) C./ (σ Tp.↑) 
          ≡⟨ cong (λ a → a C./ (σ Tp.↑)) (map-cong (λ a → Tp./-wk {t = a}) Γ) ⟩
        (map Tp.weaken Γ) ⊙ (σ Tp.↑) 
          ≡⟨ sym $ map-weaken-⊙ Γ σ ⟩
        map Tp.weaken (Γ ⊙ σ)
          ≡⟨ (map-cong (λ a → sym $ Tp./-wk {t = a}) (Γ ⊙ σ)) ⟩
        ctx-weaken (Γ C./ σ) ∎
  λ' a ⊢t           / σ = λ' (a Tp./ σ) (⊢t / σ)
  _[_] {a = a} ⊢t b / σ = ⊢substTp (sym (sub-commutes a)) ((⊢t / σ) [ b Tp./ σ ])
  ⊢s · ⊢t           / σ = (⊢s / σ) · (⊢t / σ)

  -- Weakening of terms with additional type variables lifted to
  -- well-typed terms.
  weaken : ∀ {m n} {Γ : Ctx n m} {t : Term n m} {a : Type n} →
           Γ ⊢ t ∈ a → ctx-weaken Γ ⊢ Tm.weaken t ∈ Tp.weaken a
  weaken {t = t} {a = a} ⊢t = ⊢subst refl (Tm./-wk t) (/-wk {t = a}) (⊢t / wk)

  -- Weakening of terms with additional type variables lifted to
  -- collections of well-typed terms.
  weakenAll : ∀ {m n k} {Γ : Ctx n m} {ts : Vec (Term n m) k}
                {as : Vec (Type n) k} → Γ ⊢ⁿ ts ∈ as →
                ctx-weaken Γ ⊢ⁿ map Tm.weaken ts ∈ map Tp.weaken as
  weakenAll {ts = []}    {[]}    []         = []
  weakenAll {ts = _ ∷ _} {_ ∷ _} (⊢t ∷ ⊢ts) = weaken ⊢t ∷ weakenAll ⊢ts

  -- Shorthand for single-variable type substitutions in well-typed
  -- terms.
  _[/_] : ∀ {m n} {Γ : Ctx (1 N+ n) m} {t a} →
          Γ ⊢ t ∈ a → (b : Type n) → Γ C./ sub b ⊢ t Tm./ sub b ∈ a Tp./ sub b
  ⊢t [/ b ] = ⊢t / sub b

module WellTypedLemmas where
  
  ctx-weaken-sub-vanishes : ∀ {ν n} {Γ : Ctx ν n} {a} → (ctx-weaken Γ) ctx/ (TS.sub a) ≡ Γ
  ctx-weaken-sub-vanishes {Γ = Γ} {a} = begin
    (Γ ctx/ TS.wk) ctx/ (TS.sub a) 
      ≡⟨ sym $ map-∘ (λ s → s tp/tp TS.sub a) (λ s → s tp/tp TS.wk) Γ ⟩
    (map (λ s → s tp/tp TS.wk tp/tp (TS.sub a)) Γ) 
      ≡⟨ map-cong (TypeLemmas.wk-sub-vanishes) Γ ⟩
    (map (λ s → s) Γ) ≡⟨ map-id Γ ⟩
    Γ ∎

  tm[/tp]-preserves : ∀ {ν n} {Γ : Ctx ν n} {t τ} → Γ ⊢ Λ t ∈ ∀' τ → ∀ a → Γ ⊢ (t tm[/tp a ]) ∈ τ tp[/tp a ]
  tm[/tp]-preserves {Γ = Γ} {t} {τ} (Λ p) a = 
    ctx-subst ctx-weaken-sub-vanishes (p WtTypeSubst./ (TS.sub a))
    where
      ctx-subst = subst (λ c → c ⊢ t tm[/tp a ] ∈ τ tp[/tp a ])

  postulate tm[/tm]-preserves : ∀ {ν n} {Γ : Ctx ν n} {t u a b} → 
                      b ∷ Γ ⊢ t ∈ a → Γ ⊢ u ∈ b → Γ ⊢ (t tm[/tm u ]) ∈ a

  postulate ⊢weaken-preserves : ∀ {ν n} {K : Ctx ν n} {t a} → K ⊢ t ∈ a → ctx-weaken K ⊢ tm-weaken t ∈ tp-weaken a
