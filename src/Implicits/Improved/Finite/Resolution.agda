open import Prelude

module Implicits.Improved.Finite.Resolution (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Coinduction
open import Data.Fin.Substitution
open import Implicits.Oliveira.Types TC _tc≟_
open import Implicits.Oliveira.Terms TC _tc≟_
open import Implicits.Oliveira.Contexts TC _tc≟_
open import Implicits.Oliveira.Substitutions TC _tc≟_
open import Induction
open import Induction.WellFounded
open import Relation.Binary using (Rel)

-- stacks are just a list of types
Stack : ℕ → Set
Stack ν = List (Type ν × Type ν)
{-

_List≤[_]_ : ∀ {l} {A : Set l} → List A → (_<_ : Rel A l) → List A → Set l
j List≤[ _<_ ] l = All (λ{ (a , b) → a < b ⊎ a ≡ b}) (List.zip j l)

_List<[_]_ : ∀ {l} {A : Set l} → List A → (_<_ : Rel A l) → List A → Set l
j List<[ _<_ ] l = j List≤[ _<_ ] l × Any (λ{ (a , b) → a < b}) (List.zip j l)

List<-well-founded : ∀ {l} {A : Set l} {_<_ : Rel A l} → (Well-founded _<_) →
                     Well-founded (λ j k → j List<[ _<_ ] k)
List<-well-founded wf-< List.[] = {!!}
List<-well-founded wf-< (x List.∷ l₁) = {!!}

ListRec : ∀ {l} {A : Set l} → RecStruct A l l → RecStruct (List A) l l
ListRec RecA P List.[] = Level.Lift ⊤
  where
    open import Level
ListRec RecA P (x List.∷ xs) =
  -- Either 

mutual
  data Stack' {ν} : Type ν → Set where
    [_] : (r : Type ν) → Stack' r
    _∷_ : ∀ {r' r} → (s : Stack' r) → r' ρ< (shead s) → Stack' r

  shead : ∀ {ν r} → Stack' {ν} r → Type ν
  shead [ r ] = r
  shead (_∷_ {r'} {r} s p) = r'

Stack'' : ∀ {ν} → ICtx ν → Set
Stack'' Δ = All Stack' Δ

_Stack<_ : ∀ {ν} {Δ : ICtx ν} → Stack'' Δ → Stack'' Δ → Set
Δ' Stack< Δ = {!Any ? (zip Δ' Δ)!}
-}

stack-weaken : ∀ {ν} → Stack ν → Stack (suc ν)
stack-weaken s = List.map (λ{ (r , g) → tp-weaken r , tp-weaken g }) s

-- a rule×goal pair dominates a stack if a rule is reused *and* the goal hasn't shrunk
_⊬dom_ : ∀ {ν} → (Type ν × Type ν) → (Type ν × Type ν) → Set
(r , g) ⊬dom (r' , g') = r' ≢ r ⊎ g ρ< g'

_?⊬dom_ : ∀ {ν} → (l : Type ν × Type ν) → (r : Type ν × Type ν) → Dec (l ⊬dom r)
(r , g) ?⊬dom (r' , g') with r' ≟ r
(r , g) ?⊬dom (r' , g') | no ¬p = yes (inj₁ ¬p)
(r , g) ?⊬dom (r' , g') | yes p with g ρ<? g'
(r , g) ?⊬dom (r' , g') | yes p | yes q = yes (inj₂ q)
(r , g) ?⊬dom (r' , g') | yes p | no ¬q = no (λ{ (inj₁ ¬p) → ¬p p ; (inj₂ q) → ¬q q })

infixl 5 _⊢ᵣ_
infixl 5 _&_⊢ᵣ_ _&_,_⊢_↓_
mutual
  -- Δ & s , r ⊢ a ↓ τ denotes:
  -- Under the context Δ, with stack of resolution goals s, the type a yields simple type τ.
  -- 'r' is used to keep track of the rule from the context that yielded 'a'
  -- ('a' is getting recursively refined)
  data _&_,_⊢_↓_ {ν} (Δ : ICtx ν) : Stack ν → Type ν → Type ν → SimpleType ν → Set where
    i-simp : ∀ {r s} a → Δ & s , r ⊢ simpl a ↓ a
    i-iabs : ∀ {ρ₁ ρ₂ a r s} →
             All (λ u → (r , ρ₁) ⊬dom u) s → -- subproblems decrease when recursing
             Δ & ((r , ρ₁) List.∷ s) ⊢ᵣ ρ₁ → -- domain is resolvable
             Δ & s , r ⊢ ρ₂ ↓ a → -- codomain matches
             Δ & s , r ⊢ ρ₁ ⇒ ρ₂ ↓ a
    i-tabs : ∀ {ρ a r s} b → Δ & s , r ⊢ ρ tp[/tp b ] ↓ a → Δ & s , r ⊢ ∀' ρ ↓ a

  data _&_⊢ᵣ_ {ν} (Δ : ICtx ν) : Stack ν → Type ν → Set where
    r-simp : ∀ {r τ s} → (r List.∈ Δ) → Δ & s , r ⊢ r ↓ τ → Δ & s ⊢ᵣ simpl τ
    r-iabs : ∀ {ρ₁ ρ₂ s} → ((ρ₁ List.∷ Δ) & s ⊢ᵣ ρ₂) → Δ & s ⊢ᵣ (ρ₁ ⇒ ρ₂)
    r-tabs : ∀ {ρ s} → ictx-weaken Δ & stack-weaken s ⊢ᵣ ρ → Δ & s ⊢ᵣ ∀' ρ

-- the root resolution judgements
_⊢_↓_ : ∀ {ν} → ICtx ν → Type ν → SimpleType ν → Set
Δ ⊢ r ↓ τ = Δ & List.[] , r ⊢ r ↓ τ

_⊢ᵣ_ : ∀ {ν} → ICtx ν → Type ν → Set
Δ ⊢ᵣ r = Δ & List.[] ⊢ᵣ r

module Properties where

  ρ<-trans : ∀ {ν} {a b c : Type ν} → a ρ< b → b ρ< c → a ρ< c
  ρ<-trans p q = ≤-trans p (≤⇒pred≤ _ _ q)
    where
      open import Data.Nat
      open import Data.Nat.Properties
      open import Relation.Binary
      open DecTotalOrder decTotalOrder using () renaming (trans to ≤-trans)

  ⊬dom-trans : ∀ {ν} {a b : Type ν} {x r} → (r , b) ⊬dom x → a ρ< b → (r , a) ⊬dom x 
  ⊬dom-trans (inj₁ x) aρ<b = inj₁ x
  ⊬dom-trans {ν} {a} {b} {x = x} (inj₂ y) aρ<b = inj₂ (ρ<-trans {a = a} {b = b} {c = proj₂ x} aρ<b y)

  {-
  all-⊬dom-trans : ∀ {ν} {a b : Type ν} {r s} → All (_⊬dom_ (r , b)) s → a ρ< b →
                   All (_⊬dom_ (r , a)) s
  all-⊬dom-trans {a = a} {b = b} {r} p aρ<b = All.map (λ{ x → ⊬dom-trans x aρ<b}) p

  lem : ∀ {ν} {Δ : ICtx ν} {s a b r τ} → Δ & s , a ⊢ r ↓ τ → b ρ< a → Δ & s , b ⊢ r ↓ τ
  lem (i-simp τ) aρ<b = i-simp τ
  lem (i-iabs x x₁ p) aρ<b = i-iabs {!all-⊬dom-trans x aρ<b!} {!!} (lem p aρ<b)
  lem (i-tabs b₁ p) aρ<b = {!!}
  -}
