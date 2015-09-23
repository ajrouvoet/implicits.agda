open import Prelude hiding (id; _>>=_)

module Implicits.Oliveira.Types.Unification (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Implicits.Oliveira.Types TC _tc≟_
open import Implicits.Oliveira.Types.Unification.McBride TC _tc≟_ as McBride using (
  substitute; asub; AList; _//_) public
open import Data.Vec.Properties
open import Data.Nat as N using ()
open import Data.Nat.Properties.Simple
open import Category.Monad

open import Data.Fin.Substitution
open import Implicits.Oliveira.Substitutions TC _tc≟_
open import Implicits.Oliveira.Types.Unification.Types TC _tc≟_ public
open import Implicits.Oliveira.Substitutions.Lemmas TC _tc≟_
open McBride using (substitute; asub; AList; ASub; _//_; asub-weaken) public

private
  module M = MetaTypeMetaSubst
  module T = MetaTypeTypeSubst

Unifiable : ∀ {m ν} → (MetaType m ν) → SimpleType ν → Set
Unifiable {m} a b = ∃ λ u → McBride.mgu a (simpl b)  ≡ just (zero , u)

-- Just a bit stricter than mcbride.mgu
-- We require here as well that all meta variables are instantiated
-- (this is equivalent to the ⊢unamb constraint in Oliveira)
mgu : ∀ {m ν} (a : MetaType m ν) → (b : SimpleType ν) → Maybe (Unifiable a b)
mgu a b with McBride.mgu a (simpl b)
mgu a b | just (zero , u) = just (u , refl)
mgu a b | just (suc m , _) = nothing
mgu a b | nothing = nothing

meta-weaken = M.weaken
smeta-weaken = M.smeta-weaken
metatp-weaken = T.weaken
open-meta = M.open-meta

postulate alist-zero-vanishes : ∀ {ν x} (u : AList ν zero zero) → from-meta ((to-meta x) M./ (asub u)) ≡ x
postulate mgu-id : ∀ {ν} → (a : SimpleType ν) → Unifiable {m = zero} (simpl (to-smeta a)) a

postulate mgu-sound : ∀ {m ν} → (a : MetaType m ν) → (b : SimpleType ν) →
                      mgu a b ≡ nothing → ¬ Unifiable a b
postulate mgu-unifies : ∀ {m ν} (a : MetaType m ν) (b : SimpleType ν) → (u : Unifiable a b) →
                        from-meta (a M./ (asub (proj₁ u))) ≡ (simpl b)

postulate to-meta-zero-vanishes : ∀ {ν} {a : Type ν} → from-meta (to-meta {zero} a) ≡ a
-- to-meta-zero-vanishes {a = a} = {!!}
