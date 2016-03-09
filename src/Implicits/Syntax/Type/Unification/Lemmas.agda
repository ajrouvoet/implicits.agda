module Implicits.Syntax.Type.Unification.Lemmas where

open import Prelude
open import Data.Nat.Properties.Simple
open import Data.Maybe as Maybe

open import Implicits.Syntax
open import Implicits.Syntax.Type.Unification hiding (open-meta)
open import Implicits.Substitutions
open import Implicits.Substitutions.Lemmas.MetaType

open MetaTypeMetaSubst
open MetaTypeMetaLemmas

open import Relation.Binary.HeterogeneousEquality as H using ()

-- the following properties of mgu are assumed to hold here but have been proven by
-- Conor McBride (and verified using the LEGO dependently typed language)

postulate sound : ∀ {m ν} (a : MetaType m ν) (b : SimpleType ν) →
                  Maybe.All (Unifier a b) (mgu a b)

postulate complete : ∀ {m ν} (a : MetaType m ν) (b : SimpleType ν) u →
                     Unifier a b u →
                     Is-just (mgu a b)

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

postulate mvar-unifiable : ∀ {ν m} (n : Fin m) (τ : SimpleType ν) → Unifiable (simpl (mvar n)) τ
-- mvar-unifiable = {!!}

unifiable-subst : ∀ {m m' ν} {a : MetaType m ν} {a' : MetaType m' ν} {τ} → (m-eq : m ≡ m') →
                  a H.≅ a' → Unifiable a τ → Unifiable a' τ
unifiable-subst refl H.refl p = p

open-meta-◁-unifiable : ∀ {m ν} (a : MetaType m (suc ν)) τ →
                        ◁-Unifiable (∀' a) τ → ◁-Unifiable (open-meta a) τ
open-meta-◁-unifiable {m} a τ p =
    unifiable-subst (begin suc (a ◁m₁ N+ m)
      ≡⟨ sym $ +-suc (a ◁m₁) m ⟩
    (a ◁m₁) N+ suc m
      ≡⟨ cong (flip _N+_ (suc m)) (sym $ open-meta-◁m₁ zero a) ⟩
    (open-meta a ◁m₁) N+ suc m ∎
  ) (H.sym (open-meta-◁m a)) p
