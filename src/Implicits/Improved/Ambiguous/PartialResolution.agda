open import Prelude hiding (All; module All; _>>=_)

module Implicits.Improved.Ambiguous.PartialResolution (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Coinduction
open import Data.Fin.Substitution
open import Data.List.Any
open Membership-≡
open import Implicits.Oliveira.Types TC _tc≟_
open import Implicits.Oliveira.Terms TC _tc≟_
open import Implicits.Oliveira.Contexts TC _tc≟_
open import Implicits.Oliveira.Substitutions TC _tc≟_
open import Implicits.Oliveira.Substitutions.Lemmas TC _tc≟_
open import Implicits.Improved.Ambiguous.Resolution TC _tc≟_
open import Implicits.Oliveira.Types.Unification TC _tc≟_
open SyntaxDirected

open import Category.Monad
open import Category.Functor
open import Category.Monad.Partiality as P

open import Data.Maybe using (monad; functor)
private module MaybeF {f} = RawFunctor (functor {f})

open MaybeF
open P.Workaround

_?⊥P : ∀ (A : Set) → Set₁
A ?⊥P =  (Maybe A) ⊥P

-- Resolution programs
ResP : ∀ {ν} → (ICtx ν) → Type ν → Set₁
ResP Δ r = (Δ ⊢ᵣ r) ?⊥P

-- Matching first programs
ResM1 : ∀ {ν} → (ICtx ν) → SimpleType ν → Set₁
ResM1 Δ τ = (∃ λ r → r List.∈ Δ × Δ ⊢ r ↓ τ) ?⊥P

-- Matching programs
ResM : ∀ {ν} → (ICtx ν) → Type ν → SimpleType ν → Set₁
ResM Δ r τ = (Δ ⊢ r ↓ τ) ?⊥P

module M = MetaTypeMetaSubst

_?>>=_ : ∀ {A B : Set} → A ?⊥P → (f : A → B ?⊥P) → B ?⊥P
x ?>>= f = x >>= (λ{ (just y) → f y ; nothing → now nothing })

mutual
  private
    ResM' : ∀ {m ν} → (ICtx ν) → MetaType m ν → SimpleType ν → Set₁
    ResM' Δ r τ = (∃ λ u → Δ ⊢ from-meta (r M./ u) ↓ τ) ?⊥P

    -- match' uses MetaType m ν instead of Type ν to be able to distinguish unification variables
    -- from other, non-unifiable tvars.
    -- The difference is subtle but the gist is that we can only unify variables that we open
    -- during matching. Any variables that are already open in the context are fixed.
    match' : ∀ {ν m} (Δ : ICtx ν) → (τ : SimpleType ν) → (r' : MetaType m ν) → ResM' Δ r' τ 
    -- For rule types we first check if b matches our query τ.
    -- If this is the case, we use the unifier to instantiate the unification vars in a and
    -- recursively try to resolve the result.
    -- If that succeeds as well, we use i-iabs to return a result
    match' Δ τ (a ⇒ b) = later (♯ (match' Δ τ b >>= lem))
      where
        lem : Maybe (∃ λ u → Δ ⊢ (from-meta (b M./ u)) ↓ τ) → ResM' Δ (a ⇒ b) τ
        lem (just (u , b/u↓τ)) =
          resolve Δ (from-meta (a M./ u)) >>=
            (λ{ (just Δ⊢ᵣa) → now (just (u , (i-iabs (♯ Δ⊢ᵣa) b/u↓τ))) ; nothing → now nothing })
            -- this is the inlined version of the following, which failed productivity checking:
            -- (λ Δ⊢ᵣa → now (just (u , (i-iabs (♯ Δ⊢ᵣa) b/u↓τ))))
        lem nothing = now nothing

    -- On type vars we simply open it up, adding the tvar to the set of unification variables.
    -- and recursively try to match.
    -- If matching succeeds, we can use i-tabs to return a result
    match' Δ τ (∀' a) = later (♯ ((match' Δ τ (open-meta a)) >>= (λ x → now (lem <$> x))))
      where
        lem : (∃ λ u → Δ ⊢ (from-meta ((open-meta a) M./ u)) ↓ τ) →
            ∃ λ u' → Δ ⊢ (from-meta (∀' a M./ u')) ↓ τ
        lem x = {!!}

    -- The only thing left to do is to try and unify τ and x.
    -- If we succeed, we use  i-simpl to return a result.
    match' Δ τ (simpl x) with mgu (simpl x) τ 
    match' Δ τ (simpl x) | just (u , p) =
      now (just (
        asub u ,
        subst (λ a → Δ ⊢ a ↓ τ) (sym $ mgu-unifies (simpl x) τ (u , p)) (i-simp τ)
      ))
    match' Δ τ (simpl x) | nothing = now nothing

  -- match defers to match', which concerns itself with MetaTypes.
  -- If match' finds a match, we can use the fact that we have zero unification variables open here
  -- to show that we found the right thing.
  match : ∀ {ν} (Δ : ICtx ν) → (r : Type ν) → (τ : SimpleType ν) → ResM Δ r τ 
  match Δ a τ = (match' Δ τ (to-meta {zero} a)) >>= (λ x → now (lem <$> x))
    where
      eq : ∀ {ν} {a : Type ν} {s} → from-meta (to-meta {zero} a M./ s) ≡ a
      eq {a = a} {s = []} = begin
        from-meta (M._/_ (to-meta {zero} a) [])
          ≡⟨ cong (λ q → from-meta q) (MetaTypeMetaLemmas.a/[]-vanishes (to-meta {zero} a)) ⟩
        from-meta (to-meta {zero} a)
          ≡⟨ to-meta-zero-vanishes ⟩
        a ∎
      lem : ∃ (λ u → Δ ⊢ from-meta (to-meta {zero} a M./ u) ↓ τ) → Δ ⊢ a ↓ τ
      lem ([] , proj₂) = subst (λ u → Δ ⊢ u ↓ τ) eq proj₂
        

  match1st : ∀ {ν} {Δ : ICtx ν} → (ρs : ICtx ν) → ρs ⊆ Δ → (τ : SimpleType ν) → ResM1 Δ τ
  match1st List.[] ρs⊆Δ  a = now nothing
  match1st {Δ = Δ} (x List.∷ ρs) ρs⊆Δ a = match Δ x a >>= recoverOnFail
    where
      recoverOnFail : Maybe (Δ ⊢ x ↓ a) → ResM1 Δ a
      recoverOnFail (just r↓a) = now (just (x , (ρs⊆Δ (here refl) , r↓a)))
      recoverOnFail nothing = match1st ρs (λ y → ρs⊆Δ (there y)) a

  -- resolution in ResP
  resolve : ∀ {ν} (Δ : ICtx ν) (a : Type ν) → ResP Δ a
  resolve Δ (simpl x) = match1st {Δ = Δ} Δ id x >>= (
      λ v → now ((λ{ (r , r∈Δ , r↓x) → r-simp r∈Δ r↓x }) <$> v)
    )
  resolve Δ (a ⇒ b) = resolve (a List.∷ Δ) b >>= (λ v → now ((λ x → r-iabs (♯ x)) <$> v))
  resolve Δ (∀' a) = resolve (ictx-weaken Δ) a >>= (λ v → now ((λ x → r-tabs (♯ x)) <$> v))
