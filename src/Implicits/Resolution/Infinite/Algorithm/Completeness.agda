open import Prelude hiding (All; module All; _>>=_; ⊥; sym)

module Implicits.Resolution.Infinite.Algorithm.Completeness (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Data.Bool
open import Data.Unit.Base
open import Data.Maybe as Maybe using ()
open import Coinduction
open import Data.Fin.Substitution
open import Data.List.Any hiding (tail)
open Membership-≡
open import Implicits.Syntax TC _tc≟_
open import Implicits.Substitutions TC _tc≟_
open import Implicits.Substitutions.Lemmas.MetaType TC _tc≟_
open import Implicits.Syntax.Type.Unification TC _tc≟_ as Unification hiding (complete)
open import Implicits.Resolution.Infinite.Resolution TC _tc≟_
open import Implicits.Resolution.Infinite.Algorithm TC _tc≟_
open import Data.Fin.Substitution
open import Relation.Binary.HeterogeneousEquality as H using ()
module HR = H.≅-Reasoning

open import Category.Monad.Partiality as P
open Workaround
open import Category.Monad.Partiality.All using (All; module Alternative)
open Alternative renaming (sound to AllP-sound) hiding (complete)

open import Category.Functor
private module MaybeFunctor {f} = RawFunctor (Maybe.functor {f})

module Lemmas where

  {-}
  from-to-meta-↓τ : ∀ {ν} {Δ : ICtx ν} {a τ} →
                    ∃ (λ u → Δ ⊢ from-meta (to-meta {zero} a MetaTypeMetaSubst./ u) ↓ τ) →
                    Δ ⊢ a ↓ τ
  from-to-meta-↓τ {Δ = Δ} {τ = τ} ([] , proj₂) =
    subst (λ u → Δ ⊢ u ↓ τ) from-to-meta-/-vanishes proj₂

  from-to-meta-↓τ' : ∀ {ν} {Δ : ICtx ν} {a τ} →
                     Δ ⊢ a ↓ τ → ∃ (λ u → Δ ⊢ from-meta (to-meta {zero} a MetaTypeMetaSubst./ u) ↓ τ)
  from-to-meta-↓τ' {Δ = Δ} {a} {τ} x =
    MetaTypeMetaSubst.id , subst (λ u → Δ ⊢ u ↓ τ) (Prelude.sym from-to-meta-/-vanishes) x
  -}

  _◁m : ∀ {ν m} (r : MetaType m ν) → ∃ (flip MetaType ν)
  _◁m {m} (simpl x) = , simpl x
  (a ⇒ b) ◁m = b ◁m
  ∀' r ◁m = , open-meta (proj₂ (r ◁m))

  ◁-Unifiable : ∀ {m ν} → MetaType m ν → SimpleType ν → Set
  ◁-Unifiable x τ = Unifiable (proj₂ (x ◁m)) τ

  unifiable-subst : ∀ {m m' ν} {a : MetaType m ν} {a' : MetaType m' ν} {τ} → (m-eq : m ≡ m') →
                    a H.≅ a' → Unifiable a τ → Unifiable a' τ
  unifiable-subst refl H.refl p = p

  open-meta-◁m : ∀ {ν m} (a : MetaType m (suc ν)) →
                 (proj₂ ((open-meta a) ◁m)) H.≅ open-meta (proj₂ (a ◁m))
  open-meta-◁m (a ⇒ b) = open-meta-◁m b
  open-meta-◁m (∀' a) = {!!}
    where open MetaTypeMetaSubst hiding (open-meta)
  open-meta-◁m (simpl (tvar zero)) = H.refl
  open-meta-◁m (simpl (tvar (suc x))) =
    H.cong (λ u → proj₂ (zero , u)) (H.≡-to-≅ (MetaTypeTypeLemmas.lookup-sub-↑⋆ zero x))
  open-meta-◁m (simpl (mvar x)) = H.refl
  open-meta-◁m (simpl (a →' b)) = H.refl
  open-meta-◁m (simpl (tc c)) = H.refl

  open-meta-◁m-m : ∀ {ν m} (a : MetaType m (suc ν)) →
                 (proj₁ ((open-meta a) ◁m)) ≡ suc (proj₁ (a ◁m))
  open-meta-◁m-m a = {!!}

  ↓-◁-unifiable : ∀ {ν} {Δ : ICtx ν} {r τ} → Δ ⊢ r ↓ τ → ◁-Unifiable (to-meta {zero} r) τ
  ↓-◁-unifiable (i-simp τ) = mgu-id τ
  ↓-◁-unifiable (i-iabs x p) = ↓-◁-unifiable p 
  ↓-◁-unifiable (i-tabs {ρ = a} b p) = lem₂ a b (↓-◁-unifiable p)
    where
      -- lem₁: because a tp[/tp b] ≡ (open-meta a M./ M.sub b)
      -- so let's define u ≔ the unifier of a tp[/tp b] and τ
      -- then (to-meta b) ∷ u is a unifier for a and τ
      postulate lem₁ : ∀ {ν} (a : Type (suc ν)) b {τ} →
                        ◁-Unifiable (to-meta {zero} (a tp[/tp b ])) τ →
                        ◁-Unifiable (open-meta (to-meta {zero} a)) τ

      -- goal:
      --   Unifiable (proj₂ ((to-meta {zero} (∀' a)) ◁m)) τ ≡⟨ ? ⟩
      --   Unifiable (proj₂ ((∀' (to-meta {zero} a)) ◁m)) τ ≡⟨ ? ⟩
      --   Unifiable (proj₂ (, open-meta (proj₂ ((to-meta a) ◁m)))) τ ≡⟨ ? ⟩
      --   Unifiable (proj₂ ((open-meta (to-meta {zero} a)) ◁m)) τ
      -- completing the proof with (lem₁ a b p)
      postulate lem₂ : ∀ {ν} (a : Type (suc ν)) b {τ} →
                       ◁-Unifiable (to-meta {zero} (a tp[/tp b ])) τ →
                       ◁-Unifiable (to-meta {zero} (∀' a)) τ

private
  open import Relation.Binary.PropositionalEquality as PEq using (_≡_)
  open module PartialEq = P.Equality  {A = Bool} _≡_
  open module PartialReasoning  = P.Reasoning (PEq.isEquivalence {A = Bool})
  open Lemmas

match-u-complete : ∀ {ν m} (Δ : ICtx ν) → (τ : SimpleType ν) → (r : MetaType m ν) → ◁-Unifiable r τ →
                   AllP (Maybe.Any (const ⊤)) (match-u Δ τ r)
match-u-complete Δ τ (a ⇒ b) p = {!!}
match-u-complete {m = m} Δ τ (∀' r) u =
  _
    ≅⟨ match-u-tabs-comp Δ τ r ⟩P
  later (♯ match-u-complete Δ τ (open-meta r) u') >>=-congP lem 
  where
    lem : ∀ {ν} {v : Maybe (Sub (flip MetaType ν) (suc m) zero)} →
          Maybe.Any (const ⊤) v → AllP (Maybe.Any (const ⊤)) ((now ∘ (MaybeFunctor._<$>_ tail)) v)
    lem (just px) = now (just tt)

    u' : Unifiable (proj₂ ((open-meta r) ◁m)) τ
    u' = unifiable-subst (Prelude.sym (open-meta-◁m-m r)) (H.sym (open-meta-◁m r)) u
match-u-complete Δ τ (simpl x) u
  with mgu (simpl x) τ | Unification.complete (simpl x) τ (proj₂ u)
match-u-complete Δ τ (simpl x) _ | just _  | just _ = now (just tt)
match-u-complete Δ τ (simpl x) _ | nothing | ()

-- the trivial predicate holds for all terminating problems
trivial-allP : ∀ {a} {A : Set a} (a : A ⊥) → AllP (const ⊤) a
trivial-allP (now x) = now tt
trivial-allP (later x) = later (♯ (trivial-allP (♭ x)))

-- Match succeeds if we have a proof Δ ⊢ r ↓ τ
match-complete : ∀ {ν} (Δ : ICtx ν) → (τ : SimpleType ν) → (r : Type ν) → Δ ⊢ r ↓ τ →
                 AllP (_≡_ true) (match Δ τ r)
match-complete Δ τ r p = _
    ≅⟨ match-comp Δ τ r ⟩P
  match-u-complete Δ τ (to-meta {zero} r) (↓-◁-unifiable p) >>=-congP lem
  where
    lem : ∀ {ν} {v : Maybe (Sub (flip MetaType ν) zero zero)} →
          (Maybe.Any (const ⊤) v) → AllP (_≡_ true) (⟦ (now ∘ Maybe.is-just) v ⟧P)
    lem  (just tt) = now refl

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
  ((trivial-allP (match Δ τ x)) >>=-congP
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
