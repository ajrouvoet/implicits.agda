module Extensions.Vec where

open import Data.Product hiding (map; zip)
open import Data.Nat
open import Data.Fin
open import Data.Vec
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List as L using ()
open import Data.List.Properties
open import Relation.Binary.HeterogeneousEquality as H using ()
open ≡-Reasoning public

private
  module HR = H.≅-Reasoning

lookup⋆map : ∀ {a b : Set} {n} (v : Vec a n) (f : a → b) x →
             f (lookup x v) ≡ lookup x (map f v)
lookup⋆map [] f ()
lookup⋆map (x ∷ xs) f zero = refl
lookup⋆map (x ∷ xs) f (suc y) = lookup⋆map xs f y

∷⋆map : ∀ {a b : Set} {n} (f : a → b) (x : a) (xs : Vec a n) → map f (x ∷ xs) ≡ f x ∷ (map f xs)
∷⋆map f x [] = refl
∷⋆map f x (y ∷ xs) = cong (_∷_ (f x)) (∷⋆map f y xs)

∈⟶index : ∀ {A : Set} {n} {v : Vec A n} {a : A} → a ∈ v → ∃ λ i → lookup i v ≡ a
∈⟶index here = zero , refl
∈⟶index (there e) with ∈⟶index e
∈⟶index (there e) | i , lookup-i≡a = suc i , lookup-i≡a

∈⋆map : ∀ {A B : Set} {n} {v : Vec A n} {a} → a ∈ v → (f : A → B) → (f a) ∈ (map f v)
∈⋆map here f = here
∈⋆map (there a∈v) f = there (∈⋆map a∈v f)

∷-cong : ∀ {l n n'} {A : Set l} {x : A} {xs : Vec A n} {xs' : Vec A n'} →
         n ≡ n' →
         xs H.≅ xs' →
         x ∷ xs H.≅ x ∷ xs'
∷-cong refl H.refl = H.refl

fromList-map : ∀ {l} {A B : Set l} (f : A → B) (xs : L.List A) →
               (fromList ((L.map f xs))) H.≅ (map f (fromList xs))
fromList-map f L.[] = H.refl
fromList-map f (x L.∷ xs) = ∷-cong (length-map _ xs) (fromList-map f xs)

length-toList : ∀ {A : Set } {n} (v : Vec A n) → L.length (toList v) ≡ n
length-toList [] = refl
length-toList (x ∷ v) = cong suc (length-toList v)

length-map-toList : ∀ {A B : Set} {n} {f : A → B} (v : Vec A n) → L.length (L.map f (toList v)) ≡ n
length-map-toList {n = n} {f} v = begin
  L.length (L.map f (toList v))
    ≡⟨ length-map f (toList v) ⟩
  L.length (toList v)
    ≡⟨ length-toList v ⟩
  n ∎

lookup-≔ : ∀ {n k} {A : Set k} (v : Vec A n) i (a : A) → lookup i (v [ i ]≔ a) ≡ a
lookup-≔ (x ∷ v) zero a = refl
lookup-≔ (x ∷ v) (suc i) a = lookup-≔ v i a

infixl 4 _⊑_
data _⊑_ {a} {A : Set a} : ∀ {n m} → Vec A n -> Vec A m -> Set where
  []  : ∀ {n} {xs : Vec A n} → [] ⊑ xs
  _∷_ : ∀ {n m} x {xs : Vec A n} {ys : Vec A m} -> xs ⊑ ys -> (x ∷ xs) ⊑ (x ∷ ys)

infixl 4 _⊒_
_⊒_ : ∀ {a} {A : Set a} {n m} → Vec A n -> Vec A m -> Set
xs ⊒ ys = ys ⊑ xs

open import Relation.Binary.Core using (Reflexive; Transitive)

⊑-refl : ∀ {a n} {A : Set a} → Reflexive (_⊑_ {A = A} {n = n})
⊑-refl {x = []} = []
⊑-refl {x = x ∷ xs} = x ∷ ⊑-refl

⊑-trans : ∀ {a n m k} {A : Set a} {xs : Vec A n} {ys : Vec A m} {zs : Vec A k} →
          xs ⊑ ys → ys ⊑ zs → xs ⊑ zs
⊑-trans [] [] = []
⊑-trans [] (x ∷ b) = []
⊑-trans (x ∷ xs) (.x ∷ ys) = x ∷ (⊑-trans xs ys)

∷ʳ-⊒ : ∀ {a} {A : Set a} (x : A) {n} (xs : Vec A n) → xs ∷ʳ x ⊒ xs
∷ʳ-⊒ x [] = []
∷ʳ-⊒ x (x₁ ∷ Σ₁) = x₁ ∷ (∷ʳ-⊒ x Σ₁)

xs⊒ys-length : ∀ {a n m} {A : Set a} {xs : Vec A n} {ys : Vec A m} → xs ⊒ ys → n ≥ m
xs⊒ys-length [] = z≤n
xs⊒ys-length (x ∷ p) = s≤s (xs⊒ys-length p)

xs⊒ys[i] : ∀ {a n m} {A : Set a} {xs : Vec A n} {ys : Vec A m} {i y} →
           xs [ i ]= y → (p : ys ⊒ xs) → ys [ inject≤ i (xs⊒ys-length p) ]= y
xs⊒ys[i] here (x ∷ q) = here
xs⊒ys[i] (there p) (x ∷ q) = there (xs⊒ys[i] p q)

-- Moar All properties

open import Data.Vec.All

all-lookup' : ∀ {a p} {A : Set a} {P : A → Set p} {k} {xs : Vec A k} {i x} →
              xs [ i ]= x → All P xs → P x
all-lookup' here (px ∷ _) = px
all-lookup' (there p) (_ ∷ xs) = all-lookup' p xs

-- proof matters; update a particular witness of a property
_All[_]≔_ : ∀ {a p} {A : Set a} {P : A → Set p} {k} {xs : Vec A k} {i x} →
            All P xs → xs [ i ]= x → P x → All P xs
[] All[ () ]≔ px
(px ∷ xs) All[ here ]≔ px' = px' ∷ xs
(px ∷ xs) All[ there i ]≔ px' = px ∷ (xs All[ i ]≔ px')
