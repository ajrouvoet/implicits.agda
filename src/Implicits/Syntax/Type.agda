open import Prelude hiding (lift; id)

module Implicits.Syntax.Type where

open import Data.Fin.Substitution
open import Data.Nat.Properties as NatProps
open import Data.Star using (Star; ε; _◅_)
open import Extensions.Nat
import Data.Vec
  
infixr 10 _→'_
infixr 10 _⇒_
 
mutual
  data SimpleType (ν : ℕ) : Set where
    tc   : ℕ → SimpleType ν
    tvar : (n : Fin ν) → SimpleType ν
    _→'_ : Type ν → Type ν → SimpleType ν

  data Type (ν : ℕ) : Set where
    simpl : SimpleType ν → Type ν
    _⇒_  : Type ν → Type ν → Type ν
    ∀'   : Type (suc ν) → Type ν

TVar : ∀ {ν} → Fin ν → Type ν
TVar = simpl ∘ tvar

is-∀' : ∀ {ν} → Type ν → Set
is-∀' (simpl x) = ⊥
is-∀' (_ ⇒ _) = ⊥
is-∀' (∀' x) = ⊤

fvars : ∀ {ν} → Type ν → List (Fin ν)
fvars (simpl (tc x)) = List.[]
fvars (simpl (tvar n)) = n List.∷ List.[]
fvars (simpl (x →' y)) = fvars x List.++ fvars y
fvars (a ⇒ b) = fvars a List.++ fvars b
fvars (∀' a) = List.gfilter (λ{ (Fin.zero) → nothing; (suc n) → just n}) (fvars a)

occ : ∀ {ν} → ℕ → Type ν → ℕ
occ α (simpl (tc x)) = 0
occ α (simpl (tvar n)) with α N≟ (toℕ n)
occ α (simpl (tvar n)) | yes p = 1
occ α (simpl (tvar n)) | no ¬p = 0
occ α (simpl (a →' b)) = occ α a N+ occ α b
occ α (a ⇒ b) = occ α a N+ occ α b
occ α (∀' b) = occ α b

module Functions where

  -- proposition that states that the given polytype
  -- is a (possibly polymorphic) function
  data IsFunction {ν : ℕ} : Type ν → Set where
    lambda : (a b : Type ν) → IsFunction (simpl $ a →' b)
    ∀'-lambda : ∀ {f} → IsFunction f → IsFunction (∀' f)

  -- decision procedure for IsFunction
  is-function : ∀ {ν} → (a : Type ν) → Dec (IsFunction a)
  is-function (simpl (tc _)) = no (λ ())
  is-function (simpl (tvar n)) = no (λ ())
  is-function (simpl (a →' b)) = yes (lambda a b)
  is-function (x ⇒ x₁) = no (λ ())
  is-function (∀' a) with is-function a
  is-function (∀' a) | yes a-is-f = yes $ ∀'-lambda a-is-f
  is-function (∀' a) | no a-not-f = no (λ{ (∀'-lambda a-is-f) → a-not-f a-is-f })

  domain : ∀ {ν} {f : Type ν} → IsFunction f → Type ν
  domain (lambda a b) = a
  domain (∀'-lambda f) = ∀' (domain f)

  codomain : ∀ {ν} {f : Type ν} → IsFunction f → Type ν
  codomain (lambda a b) = b
  codomain (∀'-lambda f) = ∀' (codomain f)

module Rules where

  -- proposition that states that the given polytype
  -- is a (possibly polymorphic) rule type
  data IsRule {ν : ℕ} : Type ν → Set where
    rule : (a b : Type ν) → IsRule (a ⇒ b)
    ∀'-rule : ∀ {f} → IsRule f → IsRule (∀' f)

  -- decision procedure for IsRule
  is-rule : ∀ {ν} → (a : Type ν) → Dec (IsRule a)
  is-rule (simpl (tc _)) = no (λ ())
  is-rule (simpl (tvar n)) = no (λ ())
  is-rule (simpl (a →' b)) = no (λ ())
  is-rule (a ⇒ b)  = yes (rule a b)
  is-rule (∀' a) with is-rule a
  is-rule (∀' a) | yes a-is-f = yes $ ∀'-rule a-is-f
  is-rule (∀' a) | no a-not-f = no (λ{ (∀'-rule a-is-f) → a-not-f a-is-f })

  domain : ∀ {ν} {f : Type ν} → IsRule f → Type ν
  domain (rule a b) = a
  domain (∀'-rule f) = ∀' (domain f)

  codomain : ∀ {ν} {f : Type ν} → IsRule f → Type ν
  codomain (rule a b) = b
  codomain (∀'-rule f) = ∀' (codomain f)

  to-function : ∀ {ν} {f : Type ν} → IsRule f → Type ν
  to-function (rule a b) = simpl (a →' b)
  to-function (∀'-rule f) = ∀' (to-function f)

-- decidable equality on types
_≟_ : ∀ {ν} → (a b : Type ν) → Dec (a ≡ b)
simpl (tc x) ≟ simpl (tc y) with x N≟ y
simpl (tc x) ≟ simpl (tc y) | yes p = yes (cong (simpl ∘ tc) p)
simpl (tc x) ≟ simpl (tc y) | no ¬p = no (λ x=y → ¬p $ helper x=y )
  where
    helper : ∀ {x y} → (simpl (tc x)) ≡ (simpl (tc y)) → x ≡ y
    helper refl = refl
simpl (tc x) ≟ simpl (tvar n) = no (λ ())
simpl (tc x) ≟ simpl (x₁ →' x₂) = no (λ ())
simpl (tvar n) ≟ simpl (tc x) = no (λ ())
simpl (tvar n) ≟ simpl (tvar m) with n fin≟ m
simpl (tvar n) ≟ simpl (tvar m) | yes n≡m = yes (cong (simpl ∘ tvar) n≡m)
simpl (tvar n) ≟ simpl (tvar m) | no n≢m = no (λ x=y → n≢m $ helper x=y)
  where
    helper : ∀ {n m} → (simpl (tvar n)) ≡ (simpl (tvar m)) → n ≡ m
    helper refl = refl
simpl (tvar n) ≟ simpl (x →' x₁) = no (λ ())
simpl (a →' b) ≟ simpl (tc x₂) = no (λ ())
simpl (a →' b) ≟ simpl (tvar n) = no (λ ())
simpl (a →' b) ≟ simpl (a' →' b') with a ≟ a' | b ≟ b'
simpl (a →' b) ≟ simpl (a' →' b') | yes p | yes q = yes (cong₂ (λ u v → simpl $ u →' v) p q)
simpl (a →' b) ≟ simpl (a' →' b') | yes p | no ¬q = no (λ x → ¬q (helper x) )
   where
     helper : ∀ {a b a' b'} → (simpl $ a →' b) ≡ (simpl $ a' →' b') → b ≡ b'
     helper refl = refl
simpl (a →' b) ≟ simpl (a' →' b') | no ¬p | _ = no (λ x → ¬p (helper x) )
   where
     helper : ∀ {a b a' b'} → (simpl $ a →' b) ≡ (simpl $ a' →' b') → a ≡ a'
     helper refl = refl
simpl (tc x) ≟ (b ⇒ b₁) = no (λ ())
simpl (tvar n) ≟ (b ⇒ b₁) = no (λ ())
simpl (x →' x₁) ≟ (b ⇒ b₁) = no (λ ())
simpl (tc x) ≟ ∀' b = no (λ ())
simpl (tvar n) ≟ ∀' b = no (λ ())
simpl (x →' x₁) ≟ ∀' b = no (λ ())
(a ⇒ b) ≟ simpl x = no (λ ())
(a ⇒ b) ≟ (a' ⇒ b') with a ≟ a' | b ≟ b'
(a ⇒ b) ≟ (a' ⇒ b') | yes p | yes q = yes (cong₂ (λ u v → u ⇒ v) p q)
(a ⇒ b) ≟ (a' ⇒ b') | yes p | no ¬q = no (λ x → ¬q (helper x) )
   where
     helper : ∀ {a b a' b'} → (a ⇒ b) ≡ (a' ⇒ b') → b ≡ b'
     helper refl = refl
(a ⇒ b) ≟ (a' ⇒ b') | no ¬p | _ = no (λ x → ¬p (helper x) )
   where
     helper : ∀ {a b a' b'} → (a ⇒ b) ≡ (a' ⇒ b') → a ≡ a'
     helper refl = refl
(a ⇒ a₁) ≟ ∀' b = no (λ ())
∀' a ≟ simpl x = no (λ ())
∀' a ≟ (b ⇒ b₁) = no (λ ())
∀' a ≟ ∀' b with a ≟ b
∀' a ≟ ∀' b | yes p = yes (cong ∀' p)
∀' a ≟ ∀' b | no ¬p = no (λ u → ¬p (helper u))
    where
      helper : ∀ {ν} {a b : Type (suc ν)} → ∀' a ≡ ∀' b → a ≡ b
      helper refl = refl

-- 'head' of the context type
_◁ : ∀ {ν} → Type ν → ∃ λ μ → Type μ
simpl x ◁ = , simpl x
(a ⇒ b) ◁ = b ◁
∀' a ◁ = a ◁
