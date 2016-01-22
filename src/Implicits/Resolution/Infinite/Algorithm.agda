open import Prelude hiding (All; module All; _>>=_; ⊥; _≅⟨_⟩_; _∎)

module Implicits.Resolution.Infinite.Algorithm (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Data.Bool
open import Data.Unit.Base
open import Data.Maybe using (is-just)
open import Coinduction
open import Data.Fin.Substitution
open import Data.List.Any
open import Implicits.Syntax TC _tc≟_
open import Implicits.Substitutions TC _tc≟_
open import Implicits.Substitutions.Lemmas TC _tc≟_
open import Implicits.Syntax.Type.Unification TC _tc≟_

open import Category.Monad
open import Category.Monad.Partiality as P
open import Category.Monad.Partiality.All
private module M {f} = RawMonad (monad {f})

module _ where
  open P.Workaround

  mutual

    -- match' uses MetaType m ν instead of Type ν to be able to distinguish unification variables
    -- from other, non-unifiable tvars.
    -- The difference is subtle but the gist is that we can only unify variables that we open
    -- during matching. Any variables that are already open in the context are fixed.
    match-u' : ∀ {ν m} (Δ : ICtx ν) → (τ : SimpleType ν) → (r' : MetaType m ν) →
              (Maybe (Sub (flip MetaType ν) m zero)) ⊥P
    -- For rule types we first check if b matches our query τ.
    -- If this is the case, we use the unifier to instantiate the unification vars in a and
    -- recursively try to resolve the result.
    -- If that succeeds as well, we use i-iabs to return a result
    match-u' {ν} {m} Δ τ (a ⇒ b) = (match-u' Δ τ b) >>= λ{
        (just u) →
          later (♯ (resolve' Δ (from-meta (MetaTypeMetaSubst._/_ a u)))) >>=
            λ{ true → now (just u); false → now nothing };
        nothing → now nothing
      }

  -- On type vars we simply open it up, adding the tvar to the set of unification variables.
    -- and recursively try to match.
    -- If matching succeeds, we can use i-tabs to return a result
    match-u' Δ τ (∀' a) = (later (♯ (match-u' Δ τ (open-meta a)))) >>= (λ{
        (just (u ∷ us)) → now (just us);
        nothing → now nothing
      })

    -- The only thing left to do is to try and unify τ and x.
    -- If we succeed, we use  i-simpl to return a result.
    match-u' Δ τ (simpl x) with mgu (simpl x) τ 
    match-u' Δ τ (simpl x) | just (u , p) = now (just (asub u))
    match-u' Δ τ (simpl x) | nothing = now nothing

    match' : ∀ {ν} (Δ : ICtx ν) → (τ : SimpleType ν) → Type ν → Bool ⊥P
    match' {ν} Δ τ r = match-u' Δ τ (to-meta {zero} r) >>= (now ∘ is-just)

    match1st-recover' : ∀ {ν} (Δ : ICtx ν) → (ρs : ICtx ν) → (τ : SimpleType ν) → Bool → Bool ⊥P
    match1st-recover' _ _ _ true = now true
    match1st-recover' Δ ρs τ false = match1st' Δ ρs τ

    match1st' : ∀ {ν} (Δ : ICtx ν) → (ρs : ICtx ν) → (τ : SimpleType ν) → Bool ⊥P
    match1st' Δ List.[] _ = now false
    match1st' Δ (x List.∷ ρs) τ = match' Δ τ x >>= (match1st-recover' Δ ρs τ)

    -- resolution in ResP
    resolve' : ∀ {ν} (Δ : ICtx ν) (a : Type ν) → Bool ⊥P
    resolve' Δ (simpl x) = match1st' Δ Δ x
    resolve' Δ (a ⇒ b) = resolve' (a List.∷ Δ) b
    resolve' Δ (∀' a) = resolve' (ictx-weaken Δ) a

module _ where
  open P.Workaround using (⟦_⟧P)
  open P.Workaround.Correct
  open M

  private
    open import Relation.Binary.PropositionalEquality as PEq using (_≡_)
    open module Eq = P.Equality  {A = Bool} _≡_
    open module R  = P.Reasoning (PEq.isEquivalence {A = Bool})

  match-u : ∀ {ν m} (Δ : ICtx ν) → SimpleType ν → MetaType m ν →
            (Maybe (Sub (flip MetaType ν) m zero)) ⊥
  match-u Δ τ r = ⟦ match-u' Δ τ r ⟧P

  match : ∀ {ν} (Δ : ICtx ν) → (τ : SimpleType ν) → (r : Type ν) → Bool ⊥
  match Δ τ r = ⟦ match' Δ τ r ⟧P

  match1st-recover : ∀ {ν} (Δ : ICtx ν) → (ρs : ICtx ν) → (τ : SimpleType ν) → Bool → Bool ⊥
  match1st-recover Δ ρs τ b = ⟦ match1st-recover' Δ ρs τ b ⟧P

  match1st : ∀ {ν} (Δ : ICtx ν) → (ρs : ICtx ν) → (τ : SimpleType ν) → Bool ⊥
  match1st Δ ρs τ = ⟦ match1st' Δ ρs τ ⟧P

  resolve : ∀ {ν} (Δ : ICtx ν) (r : Type ν) → Bool ⊥
  resolve Δ r = ⟦ resolve' Δ r ⟧P

  --
  -- compositionality of resolution functions
  --

  match-comp : ∀ {ν} (Δ : ICtx ν) τ r →
               match Δ τ r ≅ ((match-u Δ τ (to-meta {zero} r)) >>= (now ∘ is-just))
  match-comp Δ τ r = match Δ τ r
    ≅⟨ >>=-hom (match-u' Δ τ (to-meta {zero} r)) _ ⟩ _>>=_
      (match-u Δ τ (to-meta {zero} r)) (now ∘ is-just) ∎

  match1st-comp : ∀ {ν} (Δ : ICtx ν) x ρs τ → match1st Δ (x List.∷ ρs) τ ≅ ((match Δ τ x) >>=
                    (match1st-recover Δ ρs τ))
  match1st-comp Δ x ρs τ =
    match1st Δ (x List.∷ ρs) τ
      ≅⟨ >>=-hom (match' Δ τ x) _ ⟩
    ((match Δ τ x) >>= (match1st-recover Δ ρs τ)) ∎

