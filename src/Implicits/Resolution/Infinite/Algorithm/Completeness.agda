open import Prelude hiding (All; module All; _>>=_; ⊥; sym)

module Implicits.Resolution.Infinite.Algorithm.Completeness where

open import Data.Bool
open import Data.Unit.Base
open import Data.Maybe as Maybe using (Is-just; to-witness)
open import Coinduction
open import Data.Fin.Substitution
open import Data.List.Any hiding (tail)
open Membership-≡
open import Data.Fin.Substitution
open import Relation.Binary.HeterogeneousEquality as H using ()
open import Induction.WellFounded

open import Implicits.Syntax
open import Implicits.Substitutions
open import Implicits.Substitutions.Lemmas.MetaType
open import Implicits.Syntax.Type.Unification
open import Implicits.Syntax.Type.Unification.Lemmas as Unification hiding (complete)
open import Implicits.Resolution.Infinite.Resolution
open import Implicits.Resolution.Infinite.Algorithm
open import Implicits.Resolution.Termination

private
  module HR = H.≅-Reasoning

open import Category.Monad.Partiality as P
open Workaround
open Workaround.Correct
open import Category.Monad.Partiality.All using (All; module Alternative)
open Alternative renaming (sound to AllP-sound) hiding (complete)

open import Category.Functor
private module MaybeFunctor {f} = RawFunctor (Maybe.functor {f})

private
  module M = MetaTypeMetaSubst

module Lemmas where

private
  open import Relation.Binary.PropositionalEquality as PEq using (_≡_)
  open module PartialEq = P.Equality  {A = Bool} _≡_
  open Lemmas

mutual
  delayed-resolve-complete : ∀ {ν} (Δ : ICtx ν) r → Δ ⊢ᵣ r → AllP (_≡_ true) (delayed-resolve Δ r)
  delayed-resolve-complete Δ r p = later (♯ (complete' Δ r p))

  resolve-context-complete : ∀ {ν m} (Δ : ICtx ν) a (u : Maybe (Sub (flip MetaType ν) m zero)) →
                            (p : Is-just u) →
                            Δ ⊢ᵣ (from-meta (a M./ (to-witness p))) → 
                            AllP Is-just (resolve-context Δ a u)
  resolve-context-complete Δ a ._ (just {x = u} px) x = 
    _ ≅⟨ resolve-context-comp Δ a u ⟩P
    delayed-resolve-complete Δ (from-meta (M._/_ a u)) x >>=-congP lem
    where
      lem : ∀ {b} → true ≡ b → AllP Is-just (map-bool u b)
      lem refl = now (just tt)

  lemx : ∀ {ν m} {Δ : ICtx ν} r c τ (u : M.MetaSub MetaType ν m zero) →
        Δ ⊢ from-meta (r M./ u M.↑tp) tp[/tp c ] ↓ τ →
        Δ ⊢ from-meta (open-meta r M./ (to-meta c ∷ u)) ↓ τ
  lemx r c τ u p = {!!}

  a/u-↓-unique : ∀ {ν m} {Δ} (a : MetaType m ν) {τ} u v →
                 Δ ⊢ from-meta (a M./ u) ↓ τ → Δ ⊢ from-meta (a M./ v) ↓ τ →
                 (a M./ u) ≡ (a M./ v)
  a/u-↓-unique (a ⇒ b) u v (i-iabs _ p) (i-iabs _ q) = {!a/u-↓-unique b u v p q!} 
  a/u-↓-unique (∀' a) u v p q = {!!}
  a/u-↓-unique (simpl x) u v p q = {!!}

  match-u-complete' : ∀ {ν m} (Δ : ICtx ν) → (τ : SimpleType ν) → (r : MetaType m ν) → (ac : m<-Acc r) →
                    ∀ u → Δ ⊢ from-meta (r M./ u) ↓ τ → 
                    AllP Is-just (match-u Δ τ r ac)
  match-u-complete' Δ τ (a ⇒ b) (acc f) u (i-iabs q p) =
    _
      ≅⟨ match-u-iabs-comp Δ τ a b f ⟩P
    match-u-complete' Δ τ b (f _ (b-m<-a⇒b a b)) u p >>=-congP lem
    where
      lem : ∀ {v : Maybe (Sub (flip MetaType _) _ zero)} → Is-just v →
            AllP Is-just (resolve-context Δ a v)
      lem x = resolve-context-complete Δ a _ x q'
        where
          -- from q : Δ ⊢ᵣ a / u
          -- we derive q' : Δ ⊢ᵣ a / x
          -- based on the idea that we have Δ ⊢ b / u ↓ τ and
          -- soundness gives us Δ ⊢ b / (to-witness x) ↓ τ.
          -- And assuming ⊢unamb b, we should have u ≡ (to-witness x)
          q' : Δ ⊢ᵣ from-meta (a M./ to-witness x )
          q' = subst (_⊢ᵣ_ Δ) {!!} q
  match-u-complete' {m = m} Δ τ (∀' r) (acc f) u (i-tabs c p) =
    _
      ≅⟨ match-u-tabs-comp Δ τ r f ⟩P
    (match-u-complete' Δ τ (open-meta r) (f _ _) (to-meta {zero} c ∷ u) (lemx r c τ u p))
      >>=-congP now∘tail-compl 
    where
      now∘tail-compl : ∀ {ν} {v : Maybe (Sub (flip MetaType ν) (suc m) zero)} →
                      Is-just v →
                      AllP Is-just ((now ∘ (MaybeFunctor._<$>_ tail)) v)
      now∘tail-compl (just px) = now (just tt)

  -- Maybe surprisingly 'u' is ignored in the proofs below.
  -- But if you think about it, it makes sense: mgu doesn't necessarily find the same unifier.
  -- All we need to know is that there is a unifier u; the structure of Δ ⊢ (a / u) ↓ τ does the rest
  match-u-complete' Δ .(tvar x) (simpl (tvar x)) ac u (i-simp .(tvar x)) =
    now (Unification.complete (simpl (tvar x)) (tvar x) u refl)
  match-u-complete' Δ .(tc x) (simpl (tc x)) ac u (i-simp .(tc x)) =
    now (Unification.complete (simpl (tc x)) (tc x) u refl)
  match-u-complete' Δ τ (simpl (mvar x)) ac u p =
    let (u' , u'-uni) = mvar-unifiable x τ in
      now (Unification.complete (simpl (mvar x)) τ u' u'-uni)
  match-u-complete' Δ ._ (simpl (a →' b)) ac u (i-simp ._) =
    now (Unification.complete (simpl (a →' b)) _ u refl)

  -- the trivial predicate holds for all terminating problems
  trivial-allP : ∀ {a} {A : Set a} (a : A ⊥) → AllP (const ⊤) a
  trivial-allP (now x) = now tt
  trivial-allP (later x) = later (♯ (trivial-allP (♭ x)))

  -- Match succeeds if we have a proof Δ ⊢ r ↓ τ
  match-complete : ∀ {ν} (Δ : ICtx ν) → (τ : SimpleType ν) → (r : Type ν) → Δ ⊢ r ↓ τ →
                  AllP (_≡_ true) (match Δ τ r)
  match-complete Δ τ r p = _
      ≅⟨ match-comp Δ τ r ⟩P
    match-u-complete' Δ τ (to-meta {zero} r) (m<-well-founded _) []
      (subst (λ z → Δ ⊢ z ↓ τ) (Prelude.sym $ from-to-meta-/-vanishes) p)
      >>=-congP lem
    where
      lem : ∀ {ν} {v : Maybe (Sub (flip MetaType ν) zero zero)} →
            (Is-just v) → AllP (_≡_ true) (⟦ (now ∘ Maybe.is-just) v ⟧P)
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
  complete' : ∀ {ν} (Δ : ICtx ν) r → Δ ⊢ᵣ r → AllP (_≡_ true) (resolve Δ r)
  complete' Δ (simpl x) (r-simp r∈Δ r↓τ) = (match1st-complete Δ Δ x r∈Δ r↓τ)
  complete' Δ (a ⇒ b) (r-iabs p) = complete' (a List.∷ Δ) b p
  complete' Δ (∀' r) (r-tabs p) = complete' (ictx-weaken Δ) r p

  complete : ∀ {ν} (Δ : ICtx ν) r → Δ ⊢ᵣ r → All (_≡_ true) (resolve Δ r)
  complete Δ r p = AllP-sound (complete' Δ r p)


module Test where

  open import Category.Monad.Partiality.All

  trivial-all : ∀ {a p} {A : Set a} (P : A → Set p) → All P never
  trivial-all p = later (♯ (trivial-all p))
