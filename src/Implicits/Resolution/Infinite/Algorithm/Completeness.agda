open import Prelude hiding (All; module All; _>>=_; ⊥; sym)

module Implicits.Resolution.Infinite.Algorithm.Completeness (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Data.Bool
open import Data.Unit.Base
open import Data.Maybe as Maybe using ()
open import Coinduction
open import Data.Fin.Substitution
open import Data.List.Any
open Membership-≡
open import Implicits.Syntax TC _tc≟_
open import Implicits.Substitutions TC _tc≟_
open import Implicits.Substitutions.Lemmas.MetaType TC _tc≟_
open import Implicits.Syntax.Type.Unification TC _tc≟_
open import Implicits.Resolution.Infinite.Resolution TC _tc≟_
open import Implicits.Resolution.Infinite.Algorithm TC _tc≟_
open import Data.Fin.Substitution
open Inductive

open import Category.Monad.Partiality as P
open Workaround
open import Category.Monad.Partiality.All using (All; module Alternative)
open Alternative renaming (sound to AllP-sound) hiding (complete)

module Lemmas where

  from-to-meta-id : ∀ {ν} {a : Type ν} {s} → from-meta (to-meta {zero} a MetaTypeMetaSubst./ s) ≡ a
  from-to-meta-id {a = a} {s = []} = begin
    from-meta (MetaTypeMetaSubst._/_ (to-meta {zero} a) [])
      ≡⟨ cong (λ q → from-meta q) (MetaTypeMetaLemmas.id-vanishes (to-meta {zero} a)) ⟩
    from-meta (to-meta {zero} a)
      ≡⟨ to-meta-zero-vanishes ⟩
    a ∎

  from-to-meta-↓τ : ∀ {ν} {Δ : ICtx ν} {a τ} →
                    ∃ (λ u → Δ ⊢ from-meta (to-meta {zero} a MetaTypeMetaSubst./ u) ↓ τ) → Δ ⊢ a ↓ τ
  from-to-meta-↓τ {Δ = Δ} {τ = τ} ([] , proj₂) = subst (λ u → Δ ⊢ u ↓ τ) from-to-meta-id proj₂

  from-to-meta-↓τ' : ∀ {ν} {Δ : ICtx ν} {a τ} →
                     Δ ⊢ a ↓ τ → ∃ (λ u → Δ ⊢ from-meta (to-meta {zero} a MetaTypeMetaSubst./ u) ↓ τ)
  from-to-meta-↓τ' {Δ = Δ} {a} {τ} x = MetaTypeMetaSubst.id , subst (λ u → Δ ⊢ u ↓ τ) (begin
    a
      ≡⟨ Prelude.sym to-meta-zero-vanishes ⟩
    from-meta (to-meta {zero} a)
      ≡⟨ Prelude.sym (cong from-meta (MetaTypeMetaLemmas.id-vanishes (to-meta {zero} a))) ⟩
    from-meta (MetaTypeMetaSubst._/_ (to-meta {zero} a) MetaTypeMetaSubst.id) ∎) x

private
  open import Relation.Binary.PropositionalEquality as PEq using (_≡_)
  open module PartialEq = P.Equality  {A = Bool} _≡_
  open module PartialReasoning  = P.Reasoning (PEq.isEquivalence {A = Bool})

match-u-complete : ∀ {ν m} (Δ : ICtx ν) → (τ : SimpleType ν) → (r : MetaType m ν) →
                   (∃ λ u → Δ ⊢ from-meta (r MetaTypeMetaSubst./ u) ↓ τ) →
                   AllP (Maybe.Any (const ⊤)) (match-u Δ τ r)
match-u-complete Δ τ r p = {!!}

-- For all terminating runs of match-u, ⊤ holds ofcourse.
-- Useful if we don't care about the returned value and have no knowledge about
-- what's going to be returned.
match-u-all : ∀ {ν m} (Δ : ICtx ν) → (τ : SimpleType ν) → (r : MetaType m ν) →
              AllP (Maybe.All (const ⊤)) (match-u Δ τ r)
match-u-all Δ τ r = {!!}

-- Match succeeds if we have a proof Δ ⊢ r ↓ τ
match-complete : ∀ {ν} (Δ : ICtx ν) → (τ : SimpleType ν) → (r : Type ν) → Δ ⊢ r ↓ τ →
                 AllP (_≡_ true) (match Δ τ r)
match-complete Δ τ r p = _
    ≅⟨ match-comp Δ τ r ⟩P
  match-u-complete Δ τ (to-meta {zero} r) (Lemmas.from-to-meta-↓τ' p) >>=-congP lem
  where
    lem : ∀ {ν} {v : Maybe (Sub (flip MetaType ν) zero zero)} →
                     (Maybe.Any (const ⊤) v) → AllP (_≡_ true) (⟦ (now ∘ Maybe.is-just) v ⟧P)
    lem  (just tt) = now refl

-- ... unit holds for all terminating runs of match.
-- Useful if we don't care about what match returns
match-all : ∀ {ν} (Δ : ICtx ν) (τ : SimpleType ν) (r : Type ν) → AllP (λ v → ⊤) (match Δ τ r)
match-all Δ τ r = _
  ≅⟨ match-comp Δ τ r ⟩P match-u-all Δ τ (to-meta {zero} r) >>=-congP (λ x → now tt)

-- 'recovery' of a non failed match succeeds
recover-true-complete : ∀ {ν} {Δ : ICtx ν} {ρs τ v} → v ≡ true →
                        AllP (_≡_ true) (match1st-recover Δ ρs τ v)
recover-true-complete refl = now refl

-- recovery of a failed match succeeds if we know that the recursive match1st succeeds
recover-false-complete : ∀ {ν} (Δ : ICtx ν) ρs τ v → AllP (_≡_ true) (match1st Δ ρs τ) →
                         AllP (_≡_ true) (match1st-recover Δ ρs τ v)
recover-false-complete Δ ρs τ true p = now refl
recover-false-complete Δ ρs τ false p = p

-- match1st succeeds if we have a proof that some r from the context
-- should be a match
match1st-complete : ∀ {ν} (Δ : ICtx ν) {r} →
                    (ρs : ICtx ν) → (τ : SimpleType ν) →
                    r List.∈ ρs → Δ ⊢ r ↓ τ →
                    AllP (_≡_ true) (match1st Δ ρs τ)
match1st-complete Δ List.[] τ () r↓τ
match1st-complete Δ (x List.∷ ρs) τ (here refl) r↓τ =
  _
    ≅⟨ match1st-comp Δ x ρs τ ⟩P
  match-complete Δ τ x r↓τ >>=-congP (λ{ v → recover-true-complete (Prelude.sym v)}) 
match1st-complete Δ (x List.∷ ρs) τ (there r∈Δ) r↓τ =
  _
    ≅⟨ match1st-comp Δ x ρs τ ⟩P
  (match-all Δ τ x >>=-congP
    (λ {v} _ → recover-false-complete Δ ρs τ v (match1st-complete Δ ρs τ r∈Δ r↓τ)))

-- Mirroring Abel & Altenkirch's work on partial type checking, we say:
-- Because resolution without an additional termination condition
-- seems to be undecidable, an appropriate completeness result would be:
-- if Δ resolves r, then the resolution algorithm searching for a proof of that fact,
-- will not fail finetely. I.e. the algorithm might diverge or succeed, but not report an error.
-- We can make this formal using the *coinductive* resolution rules
-- (Together with soundness we have a 'minimal' completeness result, because the rules allow
-- for many derivations, while the algorithm will only find *one*.)
complete : ∀ {ν} (Δ : ICtx ν) r → Δ ⊢ᵣ r → AllP (_≡_ true) (resolve Δ r)
complete Δ (simpl x) (r-simp r∈Δ r↓τ) = (match1st-complete Δ Δ x r∈Δ r↓τ)
complete Δ (a ⇒ b) (r-iabs p) = complete (a List.∷ Δ) b p
complete Δ (∀' r) (r-tabs p) = complete (ictx-weaken Δ) r p
