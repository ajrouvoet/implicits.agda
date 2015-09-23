open import Prelude hiding (id; _>>=_)

module Implicits.Oliveira.Types.Unification.Properties (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Data.Vec.Properties
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Implicits.Oliveira.Types TC _tc≟_
open import Implicits.Oliveira.Substitutions TC _tc≟_
open import Implicits.Oliveira.Types.Unification.McBride TC _tc≟_
open import Implicits.Oliveira.Substitutions.Lemmas TC _tc≟_
open import Data.Star

open MetaTypeMetaSubst

{-}
for-zero≗sub : ∀ {m ν} (a : MetaType m ν) → _≗_ (a for zero) (flip lookup (sub a))
for-zero≗sub a zero = refl
for-zero≗sub a (suc n) = begin
  (a for zero) (suc n)
    ≡⟨ refl ⟩
  (simpl (mvar n))
    ≡⟨ sym $ MetaTypeMetaLemmas.lookup-sub-↑⋆ {t = a} zero n ⟩
  lookup (suc n) (sub a) ∎
-}
