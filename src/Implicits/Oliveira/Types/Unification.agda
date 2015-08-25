open import Prelude hiding (id)

module Implicits.Oliveira.Types.Unification (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Implicits.Oliveira.Types TC _tc≟_
open import Implicits.Oliveira.Substitutions TC _tc≟_
open import Implicits.Oliveira.Substitutions.Lemmas TC _tc≟_
open import Data.Vec.Properties
open import Data.Fin.Substitution
open TypeSubst

{-
module MguSubst where
  open import Data.Fin.Substitution as S using ()
  module TS = TypeSubst

  Sub : ℕ → Set
  Sub ν = Fin ν × Type ν

  Subs : ℕ → Set
  Subs ν = List (Sub ν)

  id : ∀ {ν} → Subs ν
  id = List.[] 

  _⊙_ : ∀ {ν} → Sub ν → Subs ν → Subs ν
  _⊙_ = List._∷_

  _/_ : ∀ {ν} → Type ν → Subs ν → Type ν
  a / ss = a TS./ (List.foldl (λ σ s → σ [ proj₁ s ]≔ proj₂ s) TS.id ss)

  _∈'_ : ∀ {ν} → Fin ν → Subs ν → Set
  n ∈' ss = ∃ λ a → (n , a) List.∈ ss

  _∉'_ :  ∀ {ν} → Fin ν → Subs ν → Set
  n ∉' ss = ¬ n ∈' ss

open MguSubst
-}

mutual 

  -- subn : ∀ {n} → Fin (suc n) → Type n → Sub Type (suc n) n
  -- subn {n} x a = id {n} [ x ]≔ a

  -- TODO : every substitution should remove a type variable
  postulate mgu : ∀ {ν} → (a b : Type ν) → Dec (∃ λ σ → a / σ ≡ b)
  {-
  mgu (simpl (tc x)) (simpl (tc y)) with x tc≟ y
  mgu (simpl (tc x)) (simpl (tc .x)) | yes refl = yes (id , TypeLemmas.id-vanishes (simpl $ tc x))
  mgu (simpl (tc x)) (simpl (tc y))  | no x≢y = no (λ{ (s , tc-x/s≡y) → x≢y (helper s tc-x/s≡y) }) 
    where
        helper : ∀ {c d n m} (s : Sub Type n m) → (simpl (tc c)) / s ≡ (simpl (tc d)) → c ≡ d
        helper _ refl = refl
  mgu (simpl (tvar n)) x = yes (id [ n ]≔ x , lookup∘update n id x)
  mgu (simpl (a →' b)) (simpl (a' →' b')) with mgu a a' 
  mgu (simpl (a →' b)) (simpl (a' →' b')) | no ¬p = no (λ{ (s , p) → ¬p (s , helper a b a' b' s p) })
    where
        helper : ∀ {n m} a b a' b' (σ : Sub Type n m) →
                 (simpl $ a →' b) / σ ≡ (simpl $ a' →' b') → a / σ ≡ a'
        helper _ _ _ _ _ refl = refl
  mgu (simpl (a →' b)) (simpl (a' →' b')) | yes (s , p) with mgu b (b' / s)
  mgu (simpl (a →' b)) (simpl (a' →' b')) | yes (s , p) | yes (s' , p') = yes (s ⊙ s' , helper)
    where
      helper : (simpl (a →' b)) / (s ⊙ s') ≡ (simpl (a' →' b'))
      helper = begin
        (simpl (a →' b)) / (s ⊙ s')
          ≡⟨ refl ⟩
        simpl ((a / (s ⊙ s')) →' (b / (s ⊙ s')))
          ≡⟨ ? ⟩
        simpl ((a / s / s') →' (b / (s ⊙ s')))
          ≡⟨ ? ⟩
        (simpl (a' →' b')) ∎
  mgu (simpl (a →' b)) (simpl (a' →' b')) | yes (s , p) | no ¬p' = {!!}
  mgu (a ⇒ b) (a' ⇒ b') = {!!}
  mgu (∀' a) (∀' b) with mgu a b
  mgu (∀' a) (∀' b) | yes ( s ∷ ss , p) with s ≟ (simpl (tvar zero))
  mgu (∀' a) (∀' b) | yes ( s ∷ ss , p) | yes s≡zero = yes {!ss , ?!}
  mgu (∀' a) (∀' b) | yes ( s ∷ ss , p) | no s≢zero = {!s!}
  mgu (∀' a) (∀' b) | no ¬p = {!!}

  -- obviously "no"
  mgu (simpl (tc x)) (simpl (tvar n)) = no (λ{ (s  , ()) })
  mgu (simpl (x →' x₁)) (simpl (tvar n)) =  no (λ{ (s  , ()) })
  mgu (a ⇒ b) (simpl (tvar n)) = no (λ { (s , ()) })
  mgu (∀' x) (simpl (tvar n)) = no (λ{ (s  , ()) })
  mgu (simpl (tc x)) (simpl (x₁ →' x₂)) = no (λ { (s , ()) })
  mgu (simpl (x →' x₁)) (simpl (tc x₂)) = no (λ { (s , ()) })
  mgu (simpl a) (b ⇒ b₁) = no (λ { (s , ()) })
  mgu (simpl a) (∀' b) = no (λ { (s , ()) })
  mgu (a ⇒ a₁) (simpl x) = no (λ { (s , ()) })
  mgu (a ⇒ a₁) (∀' b) = no (λ { (s , ()) })
  mgu (∀' a) (simpl x) = no (λ { (s , ()) })
  mgu (∀' a) (b ⇒ b₁) = no (λ { (s , ()) })
  -}

  {-
  data MGU {ν} : (a b : Type ν) → Set where
    uinst : ∀ n r → MGU r (simpl $ tvar n)
    uvar : ∀ n → MGU (simpl $ tvar n) (simpl $ tvar n)
    ufun : ∀ {a b a' b'} → (u₁ : MGU a a') → MGU b (apply-mgu u₁ b') →
           MGU (simpl (a →' b)) (simpl (a' →' b'))
    urul : ∀ {a b a' b'} → (u₁ : MGU a a') → MGU b (apply-mgu u₁ b') → MGU (a ⇒ b) (a' ⇒ b')
    uabs : ∀ {a b} → MGU a b → MGU (∀' a) (∀' b)

  apply-mgu : ∀ {ν} {a b : Type ν} → MGU a b → Type ν → Type ν
  apply-mgu (uinst n r) a = a TypeSubst./ (id [ n ]≔ r)
  apply-mgu (uvar n) a = a
  apply-mgu (ufun u v) a = apply-mgu v $ apply-mgu u a
  apply-mgu (urul u v) a = apply-mgu v $ apply-mgu u a
  apply-mgu (uabs u) a = {!!}
  -}

  -- postulate unifier-unifies : ∀ {ν} {a b : Type ν} → (u : MGU a b) → apply-mgu u a ≡ b

-- mgu : ∀ {ν} → (a b : Type ν) → 
