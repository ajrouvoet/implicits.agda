open import Prelude hiding (lift; id)

module Implicits.Syntax.MetaType (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Implicits.Syntax.Type TC _tc≟_

mutual
  data MetaSimpleType (m ν : ℕ) : Set where
    tvar : Fin ν → MetaSimpleType m ν
    mvar : Fin m → MetaSimpleType m ν
    _→'_ : (a b : MetaType m ν) → MetaSimpleType m ν
    tc   : (c : TC) → MetaSimpleType m ν

  data MetaType (m ν : ℕ) : Set where
    _⇒_ : (a b : MetaType m ν) → MetaType m ν
    ∀'  : MetaType m (suc ν) → MetaType m ν
    simpl : MetaSimpleType m ν → MetaType m ν

s-tvar : ∀ {ν m} → Fin ν → MetaType m ν
s-tvar n = simpl (tvar n)

s-mvar : ∀ {ν m} → Fin m → MetaType m ν
s-mvar n = simpl (mvar n)

s-tc : ∀ {ν m} → TC → MetaType m ν
s-tc c = simpl (tc c)

mutual
  to-smeta : ∀ {m ν} → SimpleType ν → MetaSimpleType m ν
  to-smeta (tc x) = (tc x)
  to-smeta (tvar n) = (tvar n)
  to-smeta (a →' b) = (to-meta a) →' (to-meta b)

  to-meta : ∀ {m ν} → Type ν → MetaType m ν
  to-meta (simpl x) = simpl (to-smeta x)
  to-meta (a ⇒ b) = (to-meta a) ⇒ (to-meta b)
  to-meta (∀' a) = ∀' (to-meta a)

from-meta : ∀ {ν} → MetaType zero ν → Type ν
from-meta (simpl (tvar x)) = simpl (tvar x)
from-meta (simpl (mvar ()))
from-meta (simpl (tc c)) = simpl (tc c)
from-meta (a ⇒ b) = from-meta a ⇒ from-meta b
from-meta (simpl (a →' b)) = simpl (from-meta a →' from-meta b)
from-meta (∀' x) = ∀' (from-meta x)

is-m∀' : ∀ {m ν} → MetaType m ν → Set
is-m∀' (simpl x) = ⊥
is-m∀' (a ⇒ b) = ⊥
is-m∀' (∀' x) = ⊤
