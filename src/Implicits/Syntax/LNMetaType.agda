open import Prelude hiding (lift; id)

module Implicits.Syntax.LNMetaType where

open import Implicits.Syntax.Type
open import Data.Nat as Nat

mutual
  data MetaSType (m : ℕ) : Set where
    tvar : ℕ → MetaSType m
    mvar : Fin m → MetaSType m
    _→'_ : (a b : MetaType m) → MetaSType m
    tc   : ℕ → MetaSType m

  data MetaType (m : ℕ) : Set where
    _⇒_ : (a b : MetaType m) → MetaType m
    ∀'  : MetaType m → MetaType m
    simpl : MetaSType m → MetaType m

mutual

  open-meta : ∀ {m} → ℕ → MetaType m → MetaType (suc m)
  open-meta k (a ⇒ b) = open-meta k a ⇒ open-meta k b
  open-meta k (∀' a) = ∀' (open-meta (suc k) a )
  open-meta k (simpl x) = simpl (open-st k x)
    where
      open-st : ∀ {m} → ℕ → MetaSType m → MetaSType (suc m)
      open-st k (tvar x) with Nat.compare x k
      open-st .(suc (x N+ k)) (tvar x) | less .x k = tvar x
      open-st k (tvar .k) | equal .k = mvar zero
      open-st k (tvar .(suc (k N+ x))) | greater .k x = tvar (k N+ x)
      open-st k (mvar x) = mvar (suc x)
      open-st k (a →' b) = open-meta k a →' open-meta k b
      open-st k (tc x) = tc x

mutual

  data TClosedS {m} (n : ℕ) : MetaSType m → Set where
    tvar : ∀ {x} → (x N< n) → TClosedS n (tvar x)
    mvar : ∀ {x} → TClosedS n (mvar x)
    _→'_ : ∀ {a b} → TClosed n a → TClosed n b → TClosedS n (a →' b)
    tc   : ∀ {c} → TClosedS n (tc c)

  data TClosed {m} (n : ℕ) : MetaType m → Set where
    _⇒_ : ∀ {a b} → TClosed n a → TClosed n b → TClosed n (a ⇒ b)
    ∀'  : ∀ {a} → TClosed (suc n) a → TClosed n (∀' a)
    simpl : ∀ {τ} → TClosedS n τ → TClosed n (simpl τ)

to-meta : ∀ {ν} → Type ν → MetaType zero
to-meta (simpl (tc x)) = simpl (tc x)
to-meta (simpl (tvar n)) = simpl (tvar (toℕ n))
to-meta (simpl (a →' b)) = simpl (to-meta a →' to-meta b)
to-meta (a ⇒ b) = to-meta a ⇒ to-meta b
to-meta (∀' a) = ∀' (to-meta a) 

from-meta : ∀ {ν} {a : MetaType zero} → TClosed ν a → Type ν
from-meta (a ⇒ b) = from-meta a ⇒ from-meta b
from-meta (∀' a) = ∀' (from-meta a)
from-meta (simpl (tvar x)) = simpl (tvar (fromℕ≤ x))
from-meta (simpl (mvar {()}))
from-meta (simpl (a →' b)) = simpl (from-meta a →' from-meta b)
from-meta (simpl (tc {c})) = simpl (tc c)
