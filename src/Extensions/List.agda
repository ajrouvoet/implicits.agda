module Extensions.List where

open import Prelude

open import Data.List
open import Data.Maybe
open import Relation.Nullary
open import Relation.Nullary.Decidable using (map′)
open import Relation.Binary.Core using (REL; Reflexive; Transitive)
open import Relation.Binary.List.Pointwise hiding (refl)

data _[_]=_ {a} {A : Set a} : List A → ℕ → A → Set where
  here : ∀ {x xs} → (x ∷ xs) [ 0 ]= x
  there : ∀ {x y xs n} → xs [ n ]= x → (y ∷ xs) [ suc n ]= x

lookup : ∀ {a} {A : Set a} → (i : ℕ) → (l : List A) → Dec (∃ λ x → l [ i ]= x)
lookup _ [] = no (λ{ (_ , ())})
lookup zero (x ∷ l) = yes (x , here)
lookup (suc i) (_ ∷ l) = map′
  (λ{ (x , p) → x , there p})
  (λ{ (x , there p) → x , p})
  (lookup i l)

_[_]≔_ : ∀ {a} {A : Set a} → (l : List A) → Fin (length l) → A → List A
[] [ () ]≔ x
(x ∷ xs) [ zero ]≔ x' = x' ∷ xs
(x ∷ xs) [ suc i ]≔ y = xs [ i ]≔ y

-- prefix predicate for lists
infix 4 _⊑_
data _⊑_ {a} {A : Set a} : List A → List A → Set where
  [] : ∀ {ys} → [] ⊑ ys
  _∷_ : ∀ x {xs ys} → xs ⊑ ys → x ∷ xs ⊑ x ∷ ys

⊑-refl : ∀ {a} {A : Set a} → Reflexive (_⊑_ {A = A})
⊑-refl {x = []} = []
⊑-refl {x = x ∷ xs} = x ∷ ⊑-refl

⊑-trans : ∀ {a} {A : Set a} → Transitive (_⊑_ {A = A})
⊑-trans [] _ = []
⊑-trans (x ∷ p) (.x ∷ q) = x ∷ ⊑-trans p q

-- list extensions; reverse prefix relation
infix 4 _⊒_
_⊒_ : ∀ {a} {A : Set a} → List A → List A → Set
xs ⊒ ys = ys ⊑ xs

-- appending to a list gives a list extension;
-- or, appending to a list makes the original a prefix
∷ʳ-⊒ : ∀ {a} {A : Set a} (x : A) xs → xs ∷ʳ x ⊒ xs
∷ʳ-⊒ x [] = []
∷ʳ-⊒ x (x₁ ∷ Σ₁) = x₁ ∷ (∷ʳ-⊒ x Σ₁)

pointwise-length : ∀ {a b ℓ A B P l m} → Rel {a} {b} {ℓ} {A} {B} P l m → length l ≡ length m
pointwise-length [] = refl
pointwise-length (x∼y ∷ p) = cong suc (pointwise-length p)

[-]=-length : ∀ {a} {A : Set a} {L : List A} {i x} → L [ i ]= x → i < length L
[-]=-length here = s≤s z≤n
[-]=-length (there p) = s≤s ([-]=-length p)
