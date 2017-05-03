module Extensions.ListFirst where

open import Prelude hiding (_⊔_)

open import Data.Product
open import Data.List
open import Data.List.Any
open Membership-≡ hiding (find)
open import Level

-- proof that an element is the first in a vector to satisfy the predicate B
data First {a b} {A : Set a} (B : A → Set b) : (x : A) → List A → Set (a ⊔ b) where

  here  : ∀ {x : A} → (p : B x) → (v : List A) → First B x (x ∷ v)
  there : ∀ {x} {v : List A} (x' : A) → ¬ (B x') → First B x v → First B x (x' ∷ v)

-- get the witness of B x from the element ∈ First
first⟶witness : ∀ {A : Set} {B : A → Set} {x l} → First B x l → B x
first⟶witness (here p v) = p
first⟶witness (there x ¬px f) = first⟶witness f

first⟶∈ : ∀ {A : Set} {B : A → Set} {x l} → First B x l → (x ∈ l × B x)
first⟶∈ (here {x = x} p v) = here refl , p
first⟶∈ (there x' ¬px f) with (first⟶∈ f)
first⟶∈ (there x' ¬px f) | x∈l , p = there x∈l , p

-- more likable syntax for the above structure
first_∈_⇔_ : {A : Set} → A → List A → (B : A → Set) → Set
first_∈_⇔_ x v p = First p x v

-- a decision procedure to find the first element in a vector that satisfies a predicate
find : ∀ {A : Set} (P : A → Set) → ((a : A) → Dec (P a)) → (v : List A) →
       Dec (∃ λ e → first e ∈ v ⇔ P)
find P dec [] = no (λ{ (e , ()) })
find P dec (x ∷ v) with dec x
find P dec (x ∷ v) | yes px = yes (x , here px v)
find P dec (x ∷ v) | no ¬px with find P dec v
find P dec (x ∷ v) | no ¬px | yes firstv = yes (, there x ¬px (proj₂ firstv))
find P dec (x ∷ v) | no ¬px | no ¬firstv = no $ helper ¬px ¬firstv
  where
    helper : ¬ (P x) → ¬ (∃ λ e → First P e v) → ¬ (∃ λ e → First P e (x ∷ v))
    helper ¬px ¬firstv (.x , here p .v) = ¬px p
    helper ¬px ¬firstv (u  , there ._ _ firstv) = ¬firstv (u , firstv)

module FirstLemmas where

  first-unique : ∀ {A : Set} {P : A → Set} {x y v} → First P x v → First P y v → x ≡ y
  first-unique (here x v) (here y .v) = refl
  first-unique (here {x = x} px v) (there .x ¬px r) = ⊥-elim (¬px px)
  first-unique (there x ¬px l) (here {x = .x} px v) = ⊥-elim (¬px px)
  first-unique (there x' _ l) (there .x' _ r) = first-unique l r
