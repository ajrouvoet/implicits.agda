open import Prelude hiding (All; module All; _>>=_; ⊥)

module Implicits.Resolution.Infinite.Algorithm.Soundness where

open import Data.Bool
open import Data.Unit.Base
open import Data.Maybe as Maybe hiding (All)
open import Coinduction
open import Data.Fin.Substitution
open import Implicits.Syntax
open import Implicits.Substitutions
open import Implicits.Substitutions.MetaType
open import Implicits.Substitutions.Lemmas
open import Implicits.Syntax.Type.Unification
open import Implicits.Syntax.Type.Unification.Lemmas renaming (sound to mgu-sound)
open import Implicits.Resolution.Infinite.Resolution
open import Implicits.Resolution.Infinite.Algorithm
open import Implicits.Resolution.Termination
open Inductive

open import Induction.WellFounded
open import Category.Functor
open import Category.Monad.Partiality as P
open import Category.Monad.Partiality.All using (All; module Alternative)
open Alternative renaming (sound to AllP-sound)

private module MaybeFunctor {f} = RawFunctor (functor {f})

open import Extensions.Bool as B hiding (All)
open import Relation.Binary.PropositionalEquality as PEq using (_≡_)
module PR = P.Reasoning (PEq.isEquivalence {A = Bool})

private
  module M = MetaTypeMetaSubst

  postulate lem₄ : ∀ {m ν} (a : MetaType m (suc ν)) u us →
                    from-meta (((M.open-meta a) M./ (us M.↑)) M./ (M.sub u))
                      ≡ (from-meta (a M./ (us M.↑tp))) tp[/tp from-meta u ]


open-↓-∀ : ∀ {ν m} {Δ : ICtx ν} (a : MetaType m (suc ν)) τ u us →
      Δ ⊢ (from-meta ((open-meta a) M./ (u ∷ us))) ↓ τ →
      Δ ⊢ (from-meta (∀' a M./ us)) ↓ τ
open-↓-∀ {Δ = Δ} a τ u us p = (i-tabs (from-meta u) (subst (λ v → Δ ⊢ v ↓ τ) (begin
      from-meta (M._/_ (open-meta a) (u ∷ us))
        ≡⟨ cong (λ v → from-meta (M._/_ (open-meta a) v)) (sym $ us↑-⊙-sub-u≡u∷us u us) ⟩
      from-meta ((open-meta a) M./ (us M.↑ M.⊙ (M.sub u)))
        ≡⟨ cong from-meta (/-⊙ (open-meta a)) ⟩
      from-meta ((open-meta a) M./ us M.↑ M./ (M.sub u))
        ≡⟨ lem₄ a u us ⟩
      from-meta (M._/_ a (us M.↑tp)) tp[/tp from-meta u ] ∎) p))
    where open MetaTypeMetaLemmas hiding (subst)

mutual

  delayed-resolve-sound : ∀ {ν} (Δ : ICtx ν) (a : Type ν) →
                          AllP (B.All (Δ ⊢ᵣ a)) (delayed-resolve Δ a)
  delayed-resolve-sound Δ a = later (♯ (resolve'-sound Δ a))

  resolve-context-sound : ∀ {ν m} (Δ : ICtx ν) (a : MetaType m ν) b {τ v} →
                          Maybe.All (λ u → Δ ⊢ from-meta (b M./ u) ↓ τ) v →
                          AllP (Maybe.All (λ u →
                            (Δ ⊢ from-meta (a M./ u) ⇒ from-meta (b M./ u) ↓ τ))
                          ) (resolve-context Δ a v)
  resolve-context-sound Δ a b {τ = τ} (just {x = u} px) = _
    ≅⟨ resolve-context-comp Δ a u ⟩P delayed-resolve-sound Δ (from-meta (M._/_ a u)) >>=-congP lem
    where
      lem : ∀ {v} → B.All (Δ ⊢ᵣ from-meta (a M./ u)) v →
            AllP (Maybe.All (λ u → Δ ⊢ from-meta (a M./ u) ⇒ from-meta (b M./ u) ↓ τ)) (map-bool u v)
      lem (true x) = now (just (i-iabs x px))
      lem (false) = now nothing
  resolve-context-sound Δ a b nothing = now nothing

  match-u-sound : ∀ {ν m} (Δ : ICtx ν) τ (r : MetaType m ν) → (r-acc : m<-Acc r) →
                  AllP (Maybe.All (λ u → (Δ ⊢ from-meta (r M./ u) ↓ τ))) (match-u Δ τ r r-acc)
  match-u-sound Δ τ (a ⇒ b) (acc rs) = _ ≅⟨ match-u-iabs-comp Δ τ a b rs ⟩P
    match-u-sound Δ τ b (rs _ (b-m<-a⇒b a b)) >>=-congP resolve-context-sound Δ a b
  match-u-sound Δ τ (∀' r) (acc rs) = _ ≅⟨ match-u-tabs-comp Δ τ r rs ⟩P
    match-u-sound Δ τ (open-meta r) _ >>=-congP lem
    where
      lem : ∀ {v} → Maybe.All (λ u → Δ ⊢ from-meta (open-meta r M./ u) ↓ τ) v →
            AllP (Maybe.All (λ u → Δ ⊢ ∀' (from-meta (r M./ u M.↑tp)) ↓ τ ))
                ((now ∘ (MaybeFunctor._<$>_ tail)) v)
      lem (just {x = u ∷ us} px) = now (just (open-↓-∀ r τ u us px))
      lem nothing = now nothing
  match-u-sound Δ τ (simpl x) (acc rs) with mgu (simpl x) τ | mgu-sound (simpl x) τ
  match-u-sound Δ τ (simpl x) (acc rs) | just us | just x/us≡τ =
    now (just (subst (λ z → Δ ⊢ z ↓ τ) (sym x/us≡τ) (i-simp τ)))
  match-u-sound Δ τ (simpl x) (acc rs) | nothing | nothing = now nothing

  match-sound : ∀ {ν} (Δ : ICtx ν) τ r → 
                AllP (B.All (Δ ⊢ r ↓ τ)) (match Δ τ r)
  match-sound Δ τ r = _
    ≅⟨ match-comp Δ τ r ⟩P
    match-u-sound Δ τ (to-meta {zero} r) (m<-well-founded _) >>=-congP lem
    where
      eq : ∀ {ν} {a : Type ν} {s} → from-meta (to-meta {zero} a M./ s) ≡ a
      eq {a = a} {s = []} = begin
          from-meta (M._/_ (to-meta {zero} a) [])
        ≡⟨ cong (λ q → from-meta q) (MetaTypeMetaLemmas.id-vanishes (to-meta {zero} a)) ⟩
          from-meta (to-meta {zero} a)
        ≡⟨ to-meta-zero-vanishes ⟩
          a ∎

      lem : ∀ {v} → Maybe.All (λ u → (Δ ⊢ from-meta ((to-meta {zero} r) M./ u) ↓ τ)) v →
            AllP (B.All (Δ ⊢ r ↓ τ)) ((now ∘ is-just) v)
      lem (just px) = now (true (subst (λ z → Δ ⊢ z ↓ τ) eq px))
      lem nothing = now false

  match1st-recover-sound : ∀ {ν b} x (Δ ρs : ICtx ν) τ → B.All (Δ ⊢ x ↓ τ) b →
                          AllP (B.All (∃₂ λ r (r∈Δ : r List.∈ (x List.∷ ρs)) → Δ ⊢ r ↓ τ))
                                (match1st-recover Δ ρs τ b)
  match1st-recover-sound x Δ ρs τ (true p) = now (true (x , (here refl) , p))
  match1st-recover-sound x Δ ρs τ false = _
    ≅⟨ PR.sym (right-identity refl (match1st Δ ρs τ)) ⟩P
    match1st'-sound Δ ρs τ >>=-congP lem
    where
      lem : ∀ {v} → B.All (∃₂ λ r (r∈Δ : r List.∈ ρs)→ Δ ⊢ r ↓ τ) v →
            AllP (B.All (∃₂ λ r (r∈Δ : r List.∈ x List.∷ ρs) → Δ ⊢ r ↓ τ)) (now v)
      lem (true (r , r∈ρs , p)) = now (true (r , (there r∈ρs) , p))
      lem false = now false

    -- {!match1st'-sound Δ ρs τ!}

  match1st'-sound : ∀ {ν} (Δ ρs : ICtx ν) τ →
                    AllP (B.All (∃₂ λ r (r∈Δ : r List.∈ ρs) → Δ ⊢ r ↓ τ)) (match1st Δ ρs τ)
  match1st'-sound Δ List.[] τ = now false
  match1st'-sound Δ (x List.∷ ρs) τ = _
    ≅⟨ match1st-comp Δ x ρs τ ⟩P
    match-sound Δ τ x >>=-congP match1st-recover-sound x Δ ρs τ

  resolve'-sound : ∀ {ν} (Δ : ICtx ν) r → AllP (B.All (Δ ⊢ᵣ r)) (resolve Δ r)
  resolve'-sound Δ (simpl x) = _
    ≅⟨ PR.sym (right-identity refl (match1st Δ Δ x)) ⟩P
    match1st'-sound Δ Δ x >>=-congP (λ x → now (B.all-map x (λ{ (r , r∈Δ , p) → r-simp r∈Δ p })))
  resolve'-sound Δ (a ⇒ b) = _
    ≅⟨ PR.sym (right-identity refl (resolve (a List.∷ Δ) b)) ⟩P
    resolve'-sound (a List.∷ Δ) b >>=-congP (λ x → now (B.all-map x r-iabs))
  resolve'-sound Δ (∀' r) = _
    ≅⟨ PR.sym (right-identity refl (resolve (ictx-weaken Δ) r)) ⟩P
    resolve'-sound (ictx-weaken Δ) r >>=-congP (λ x → now (B.all-map x r-tabs))

  -- Soundness means:
  -- for all terminating runs of the algorithm we have a finite resolution proof.
  sound : ∀ {ν} (Δ : ICtx ν) r → All (B.All (Δ ⊢ᵣ r)) (resolve Δ r)
  sound Δ r = AllP-sound (resolve'-sound Δ r)
