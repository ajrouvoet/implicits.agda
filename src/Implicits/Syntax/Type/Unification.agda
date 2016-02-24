open import Prelude hiding (id; _>>=_)

module Implicits.Syntax.Type.Unification where

open import Data.Maybe as Maybe
open import Data.Unit
open import Implicits.Syntax
open import Implicits.Syntax.Type.Unification.McBride as McBride using (
  substitute; asub; AList; _//_) public
open import Data.Vec.Properties
open import Data.Nat as N using ()
open import Data.Nat.Properties.Simple
open import Category.Monad

open import Data.Fin.Substitution
open import Implicits.Substitutions
open import Implicits.Syntax.MetaType public
open import Implicits.Substitutions.Lemmas
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

Unifier : ∀ {m ν} → (MetaType m ν) → SimpleType ν → (Sub (flip MetaType ν) m zero) → Set
Unifier {m} a b u = from-meta (a M./ u) ≡ (simpl b)

Unifiable : ∀ {m ν} → (MetaType m ν) → SimpleType ν → Set
Unifiable a τ = ∃ (Unifier a τ)

-- the following properties of mgu are assumed to hold here but have been proven by
-- Conor McBride (and verified using the LEGO dependently typed language)

postulate sound : ∀ {m ν} (a : MetaType m ν) (b : SimpleType ν) →
                      Maybe.All (Unifier a b) (mgu a b)

postulate complete : ∀ {m ν} (a : MetaType m ν) (b : SimpleType ν) {u} →
                         Unifier a b u →
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

from-to-meta-/-vanishes : ∀ {ν} {a : Type ν} {s} →
                          from-meta (to-meta {zero} a MetaTypeMetaSubst./ s) ≡ a
from-to-meta-/-vanishes {a = a} {s = []} = begin 
  from-meta (MetaTypeMetaSubst._/_ (to-meta {zero} a) [])
    ≡⟨ cong (λ q → from-meta q) (MetaTypeMetaLemmas.id-vanishes (to-meta {zero} a)) ⟩
  from-meta (to-meta {zero} a)
    ≡⟨ to-meta-zero-vanishes ⟩
  a ∎

mgu-id : ∀ {ν} → (a : SimpleType ν) → Unifiable {m = zero} (simpl (to-smeta a)) a
mgu-id a = [] , (begin
  from-meta (MetaTypeMetaSubst._/_ (simpl (to-smeta a)) [])
    ≡⟨ from-to-meta-/-vanishes ⟩
  simpl a ∎)
