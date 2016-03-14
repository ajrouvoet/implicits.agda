module Extensions.Vec where

open import Data.Product hiding (map; zip)
open import Data.Nat
open import Data.Fin
open import Data.Vec
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List as L using ()
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
  where open import Data.List.Properties
  
open import Data.List as List
open import Data.List.Properties

length-toList : ∀ {A : Set } {n} (v : Vec A n) → List.length (toList v) ≡ n
length-toList [] = refl
length-toList (x ∷ v) = cong suc (length-toList v)

length-map-toList : ∀ {A B : Set} {n} {f : A → B} (v : Vec A n) → List.length (List.map f (toList v)) ≡ n
length-map-toList {n = n} {f} v = begin
  List.length (List.map f (toList v))
    ≡⟨ length-map f (toList v) ⟩
  List.length (toList v)
    ≡⟨ length-toList v ⟩
  n ∎
