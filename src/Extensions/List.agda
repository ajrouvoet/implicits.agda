module Extensions.List where

open import Prelude

open import Data.List
open import Data.Fin using (fromℕ≤; zero; suc)
open import Data.List.All hiding (lookup; map)
open import Data.Maybe hiding (All; map)
open import Relation.Nullary
open import Relation.Nullary.Decidable using (map′)
open import Relation.Binary.Core using (REL; Reflexive; Transitive)
open import Relation.Binary.List.Pointwise hiding (refl; map)

data _[_]=_ {a} {A : Set a} : List A → ℕ → A → Set where
  here : ∀ {x xs} → (x ∷ xs) [ 0 ]= x
  there : ∀ {x y xs n} → xs [ n ]= x → (y ∷ xs) [ suc n ]= x

[]=-functional : ∀ {a} {A : Set a} → (l : List A) → (i : ℕ) →
                   ∀ {x y : A} → l [ i ]= x → l [ i ]= y → x ≡ y
[]=-functional .(_ ∷ _) .0 here here = refl
[]=-functional .(_ ∷ _) .(suc _) (there p) (there q) = []=-functional _ _ p q

[]=-map : ∀ {a b}{A : Set a}{B : Set b}{l : List A}{i x}{f : A → B} →
            l [ i ]= x → (map f l) [ i ]= (f x)
[]=-map here = here
[]=-map (there p) = there ([]=-map p)

maybe-lookup : ∀ {a}{A : Set a} → ℕ → List A → Maybe A
maybe-lookup n [] = nothing
maybe-lookup zero (x ∷ μ) = just x
maybe-lookup (suc n) (x ∷ μ) = maybe-lookup n μ

maybe-lookup-safe : ∀ {a}{A : Set a}{l : List A} {i x} → l [ i ]= x → maybe-lookup i l ≡ just x
maybe-lookup-safe here = refl
maybe-lookup-safe (there p) = maybe-lookup-safe p

lookup : ∀ {a} {A : Set a} → (l : List A) → Fin (length l) → A
lookup [] ()
lookup (x ∷ l) zero = x
lookup (x ∷ l) (suc p) = lookup l p

dec-lookup : ∀ {a} {A : Set a} → (i : ℕ) → (l : List A) → Dec (∃ λ x → l [ i ]= x)
dec-lookup _ [] = no (λ{ (_ , ())})
dec-lookup zero (x ∷ l) = yes (x , here)
dec-lookup (suc i) (_ ∷ l) = map′
  (λ{ (x , p) → x , there p})
  (λ{ (x , there p) → x , p})
  (dec-lookup i l)

all-lookup : ∀ {a} {A : Set a} {l : List A} {i x p P} → l [ i ]= x → All {p = p} P l → P x
all-lookup here (px ∷ l) = px
all-lookup (there i) (px ∷ l) = all-lookup i l

infixl 10 _[_]≔_
_[_]≔_ : ∀ {a} {A : Set a} → (l : List A) → Fin (length l) → A → List A
[] [ () ]≔ x
(x ∷ xs) [ zero ]≔ x' = x' ∷ xs
(x ∷ xs) [ suc i ]≔ y = xs [ i ]≔ y

module _ where
  open import Data.List.Any
  open Membership-≡

  _[_]≔'_ : ∀ {a} {A : Set a}{x} → (l : List A) → x ∈ l → A → List A
  [] [ () ]≔' y
  (x ∷ l) [ here px ]≔' y = y ∷ l
  (x ∷ l) [ there px ]≔' y = x ∷ (l [ px ]≔' y)

  ≔'-[]= :  ∀ {a} {A : Set a}{x}{l : List A} (p : x ∈ l) → ∀ {y} → y ∈ (l [ p ]≔' y)
  ≔'-[]= (here px) = here refl
  ≔'-[]= (there p) = there (≔'-[]= p)

-- proof matters; update a particular witness of a property
_All[_]≔_ : ∀ {a p} {A : Set a} {P : A → Set p} {xs : List A} {i x} →
            All P xs → xs [ i ]= x → P x → All P xs
[] All[ () ]≔ px
(px ∷ xs) All[ here ]≔ px' = px' ∷ xs
(px ∷ xs) All[ there i ]≔ px' = px ∷ (xs All[ i ]≔ px')

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

-- indexes into a prefix point to the same element in extensions
xs⊒ys[i] : ∀ {a} {A : Set a} {xs : List A} {ys : List A} {i y} →
           xs [ i ]= y → (p : ys ⊒ xs) → ys [ i ]= y
xs⊒ys[i] here (x ∷ q) = here
xs⊒ys[i] (there p) (x ∷ q) = there (xs⊒ys[i] p q)

-- prefix is preserved by map
⊑-map : ∀ {a b} {A : Set a} {B : Set b} {xs ys : List A} {f : A → B} →
        xs ⊑ ys → map f xs ⊑ map f ys
⊑-map [] = []
⊑-map {f = f} (x ∷ p) = f x ∷ (⊑-map p)

module Pointwise where
  pointwise-length : ∀ {a b ℓ A B P l m} → Rel {a} {b} {ℓ} {A} {B} P l m → length l ≡ length m
  pointwise-length [] = refl
  pointwise-length (x∼y ∷ p) = cong suc (pointwise-length p)

  []=-length : ∀ {a} {A : Set a} {L : List A} {i x} → L [ i ]= x → i < length L
  []=-length here = s≤s z≤n
  []=-length (there p) = s≤s ([]=-length p)

  ∷ʳ[length] : ∀ {a} {A : Set a} (l : List A) x → (l ∷ʳ x) [ length l ]= x
  ∷ʳ[length] [] y = here
  ∷ʳ[length] (x ∷ Σ) y = there (∷ʳ[length] Σ y)

  all-∷ʳ : ∀ {a p} {A : Set a} {l : List A} {x} {P : A → Set p} → All P l → P x → All P (l ∷ʳ x)
  all-∷ʳ [] q = q ∷ []
  all-∷ʳ (px ∷ p) q = px ∷ (all-∷ʳ p q)

  pointwise-∷ʳ : ∀ {a b ℓ A B P l m x y} → Rel {a} {b} {ℓ} {A} {B} P l m → P x y →
                Rel {a} {b} {ℓ} {A} {B} P (l ∷ʳ x) (m ∷ʳ y)
  pointwise-∷ʳ [] q = q ∷ []
  pointwise-∷ʳ (x∼y ∷ p) q = x∼y ∷ (pointwise-∷ʳ p q)

  pointwise-lookup : ∀ {a b ℓ A B P l m i x} → Rel {a} {b} {ℓ} {A} {B} P l m →
                     l [ i ]= x → ∃ λ y → P x y
  pointwise-lookup (x∼y ∷ r) here = , x∼y
  pointwise-lookup (x∼y ∷ r) (there p) = pointwise-lookup r p

  pointwise-maybe-lookup : ∀ {a b ℓ A B P l m i x} → Rel {a} {b} {ℓ} {A} {B} P l m →
                     l [ i ]= x → ∃ λ y → maybe-lookup i m ≡ just y × P x y
  pointwise-maybe-lookup [] ()
  pointwise-maybe-lookup (x∼y ∷ r) here = , refl , x∼y
  pointwise-maybe-lookup (x∼y ∷ r) (there p) = pointwise-maybe-lookup r p

  postulate
    pointwise-[]≔ : ∀ {a b ℓ A B P l m i x y} →
                    Rel {a} {b} {ℓ} {A} {B} P l m → (p : l [ i ]= x) → (q : i < length m) → P x y →
                    Rel {a} {b} {ℓ} {A} {B} P l (m [ fromℕ≤ q ]≔ y)
  {-}
  pointwise-[]≔ [] () r
  pointwise-[]≔ (x∼y ∷ r) here (s≤s z≤n) z = z ∷ r
  pointwise-[]≔ (x∼y ∷ r) (there p) (s≤s q) z = subst (λ x → Rel _ _ x) {!!} (x∼y ∷ pointwise-[]≔ r p q z) 
  -}

open Pointwise public
