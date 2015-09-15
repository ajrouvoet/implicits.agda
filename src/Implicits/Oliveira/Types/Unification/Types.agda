open import Prelude

module Implicits.Oliveira.Types.Unification.Types (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Implicits.Oliveira.Types TC _tc≟_

data Fork : Set where
  rul : Fork
  fun : Fork

_fork≟_ : (c d : Fork) → Dec (c ≡ d)
rul fork≟ rul = yes refl
rul fork≟ fun = no (λ ())
fun fork≟ rul = no (λ ())
fun fork≟ fun = yes refl

data MetaType (m ν : ℕ) : Set where
  tvar : Fin ν → MetaType m ν
  mvar : Fin m → MetaType m ν
  fork : Fork → MetaType m ν → MetaType m ν → MetaType m ν
  ∀'   : MetaType m (suc ν) → MetaType m ν
  tc   : (c : TC) → MetaType m ν

-- [α,β⟩ is het interval of variables that are unification variables.
-- e.g. : [0, 3⟩ means the variables 0, 1 and 2 are unification variables 
to-meta : ∀ {m ν} → Type ν → MetaType m ν
to-meta (simpl (tc x)) = tc x
to-meta (simpl (tvar n)) = tvar n
to-meta (simpl (a →' b)) = fork rul (to-meta a) (to-meta b)
to-meta (a ⇒ b) = fork fun (to-meta a) (to-meta b)
to-meta (∀' a) = ∀' (to-meta a)

from-meta : ∀ {ν} → MetaType zero ν → Type ν
from-meta (tvar x) = simpl $ tvar x
from-meta (mvar ())
from-meta (fork rul a b) = from-meta a ⇒ from-meta b
from-meta (fork fun a b) = simpl $ from-meta a →' from-meta b
from-meta (∀' x) = ∀' (from-meta x)
from-meta (tc c) = simpl $ tc c

is-m∀' : ∀ {m ν} → MetaType m ν → Set
is-m∀' (tvar x) = ⊥
is-m∀' (mvar x) = ⊥
is-m∀' (fork x x₁ x₂) = ⊥
is-m∀' (∀' x) = ⊤
is-m∀' (tc c) = ⊥
