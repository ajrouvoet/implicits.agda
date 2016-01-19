open import Prelude hiding (All; module All; _>>=_; ⊥)

module Implicits.Resolution.Infinite.AlgorithmBare (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Data.Bool
open import Coinduction
open import Data.Fin.Substitution
open import Data.List.Any
open import Implicits.Syntax TC _tc≟_
open import Implicits.Substitutions TC _tc≟_
open import Implicits.Substitutions.Lemmas TC _tc≟_
open import Implicits.Resolution.Infinite.Resolution TC _tc≟_
open import Implicits.Syntax.Type.Unification TC _tc≟_

open import Category.Monad.Partiality as P

open P.Workaround

mutual
  private

    match : ∀ {ν} (Δ : ICtx ν) → (r : Type ν) → (τ : SimpleType ν) → Bool ⊥P
    match Δ a τ = match' Δ τ (to-meta {zero} a) >>= (λ{ (just _) → now true; _ → now false })
      where
        -- match' uses MetaType m ν instead of Type ν to be able to distinguish unification variables
        -- from other, non-unifiable tvars.
        -- The difference is subtle but the gist is that we can only unify variables that we open
        -- during matching. Any variables that are already open in the context are fixed.
        match' : ∀ {ν m} (Δ : ICtx ν) → (τ : SimpleType ν) → (r' : MetaType m ν) →
                (Maybe (Sub (flip MetaType ν) m zero)) ⊥P
        -- For rule types we first check if b matches our query τ.
        -- If this is the case, we use the unifier to instantiate the unification vars in a and
        -- recursively try to resolve the result.
        -- If that succeeds as well, we use i-iabs to return a result
        match' {ν} {m} Δ τ (a ⇒ b) = (match' Δ τ b) >>= λ{
            (just u) →
              later (♯ (resolve' Δ (from-meta (MetaTypeMetaSubst._/_ a u)))) >>=
                λ{ true → now (just u); false → now nothing };
            nothing → now nothing
          }

      -- On type vars we simply open it up, adding the tvar to the set of unification variables.
        -- and recursively try to match.
        -- If matching succeeds, we can use i-tabs to return a result
        match' Δ τ (∀' a) = later (♯ (match' Δ τ (open-meta a))) >>= (λ{
            (just (u ∷ us)) → now (just us);
            nothing → now nothing
          })

        -- The only thing left to do is to try and unify τ and x.
        -- If we succeed, we use  i-simpl to return a result.
        match' Δ τ (simpl x) with mgu (simpl x) τ 
        match' Δ τ (simpl x) | just (u , p) = now (just (asub u))
        match' Δ τ (simpl x) | nothing = now nothing

  match1st : ∀ {ν} {Δ : ICtx ν} → (ρs : ICtx ν) → (τ : SimpleType ν) → Bool ⊥P
  match1st List.[] a = now false
  match1st {Δ = Δ} (x List.∷ ρs) a = match Δ x a >>= recoverOnFail
    where
      recoverOnFail : Bool → Bool ⊥P
      recoverOnFail true = now true 
      recoverOnFail false = match1st {Δ = Δ} ρs a

  -- resolution in ResP
  resolve' : ∀ {ν} (Δ : ICtx ν) (a : Type ν) → Bool ⊥P
  resolve' Δ (simpl x) = match1st {Δ = Δ} Δ x
  resolve' Δ (a ⇒ b) = resolve' (a List.∷ Δ) b
  resolve' Δ (∀' a) = resolve' (ictx-weaken Δ) a

  resolve : ∀ {ν} (Δ : ICtx ν) (r : Type ν) → Bool ⊥
  resolve Δ r = ⟦ resolve' Δ r ⟧P

  _resolved? : Bool ⊥ → Bool
  now true resolved? = true
  now false resolved? = false
  later x resolved? = false

  _resolves_after_steps : ∀ {ν} (Δ : ICtx ν) (r : Type ν) → ℕ → Bool
  Δ resolves r after n steps = (run_for_steps (resolve Δ r) n) resolved?
