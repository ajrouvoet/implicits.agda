open import Prelude hiding (id; _>>=_)

module Implicits.Syntax.Type.Unification (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Data.Maybe as Maybe
open import Data.Unit
open import Implicits.Syntax TC _tc≟_
open import Implicits.Syntax.Type.Unification.McBride TC _tc≟_ as McBride using (
  substitute; asub; AList; _//_) public
open import Data.Vec.Properties
open import Data.Nat as N using ()
open import Data.Nat.Properties.Simple
open import Category.Monad

open import Data.Fin.Substitution
open import Implicits.Substitutions TC _tc≟_
open import Implicits.Syntax.MetaType TC _tc≟_ public
open import Implicits.Substitutions.Lemmas TC _tc≟_
open McBride using (substitute; asub; AList; ASub; _//_; asub-weaken) public

private
  module M = MetaTypeMetaSubst
  module T = MetaTypeTypeSubst

-- Just a bit stricter than mcbride.mgu
-- We require here as well that all meta variables are instantiated
-- (this is equivalent to the ⊢unamb constraint in Oliveira)
mgu : ∀ {m ν} (a : MetaType m ν) → (b : SimpleType ν) → Maybe (Sub (flip MetaType ν) m zero)
mgu a b with McBride.mgu a (simpl b)
mgu a b | just (zero , u) = just (asub u)
mgu a b | just (suc m , _) = nothing
mgu a b | nothing = nothing

Unifiable : ∀ {m ν} → (MetaType m ν) → SimpleType ν → (Sub (flip MetaType ν) m zero) → Set
Unifiable {m} a b u = from-meta (a M./ u) ≡ (simpl b)

-- the following properties of mgu are assumed to hold here but have been proven by
-- Conor McBride (and verified using the LEGO dependently typed language)

postulate sound : ∀ {m ν} (a : MetaType m ν) (b : SimpleType ν) →
                      Maybe.All (Unifiable a b) (mgu a b)

postulate complete : ∀ {m ν} (a : MetaType m ν) (b : SimpleType ν) {u} →
                         Unifiable a b u →
                         Maybe.Any (const ⊤) (mgu a b)

meta-weaken = M.weaken
smeta-weaken = M.smeta-weaken
open-meta = M.open-meta

to-meta-zero-vanishes : ∀ {ν} {a : Type ν} → from-meta (to-meta a) ≡ a
to-meta-zero-vanishes {a = simpl (tc x)} = refl
to-meta-zero-vanishes {a = simpl (tvar n)} = refl
to-meta-zero-vanishes {a = simpl (a →' b)} =
  cong₂ (λ u v → simpl (u →' v)) to-meta-zero-vanishes to-meta-zero-vanishes
to-meta-zero-vanishes {a = a ⇒ b} = cong₂ _⇒_ to-meta-zero-vanishes to-meta-zero-vanishes
to-meta-zero-vanishes {a = ∀' a} = cong ∀' to-meta-zero-vanishes

postulate mgu-id : ∀ {ν} → (a : SimpleType ν) → ∃ (Unifiable {m = zero} (simpl (to-smeta a)) a)
