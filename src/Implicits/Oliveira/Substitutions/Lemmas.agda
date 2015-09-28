open import Prelude renaming (lift to finlift) hiding (id; subst)

module Implicits.Oliveira.Substitutions.Lemmas (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Implicits.Oliveira.Types TC _tc≟_
open import Implicits.Oliveira.Terms TC _tc≟_
open import Implicits.Oliveira.Contexts TC _tc≟_
open import Implicits.Oliveira.WellTyped TC _tc≟_
open import Implicits.Oliveira.Substitutions TC _tc≟_
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Vec.Properties
open import Extensions.Substitution
import Category.Applicative.Indexed as Applicative
open Applicative.Morphism using (op-<$>)

module TypeLemmas where
  open import Data.Fin.Substitution.Lemmas
  open import Data.Fin.Substitution.Lemmas public using (module VarLemmas)
  open TypeSubst
  open import Data.Star using (Star; ε; _◅_)

  typeLemmas : TermLemmas Type
  typeLemmas = record { termSubst = TypeSubst.typeSubst; app-var = refl ; /✶-↑✶ = Lemma./✶-↑✶ }
    where
      module Lemma {T₁ T₂} {lift₁ : Lift T₁ Type} {lift₂ : Lift T₂ Type} where

        open Lifted lift₁ using () renaming (_↑✶_ to _↑✶₁_; _/✶_ to _/✶₁_)
        open Lifted lift₂ using () renaming (_↑✶_ to _↑✶₂_; _/✶_ to _/✶₂_)

        /✶-↑✶ : ∀ {m n} (σs₁ : Subs T₁ m n) (σs₂ : Subs T₂ m n) → 
                            (∀ k x → (simpl (tvar x)) /✶₁ σs₁ ↑✶₁ k ≡ (simpl (tvar x)) /✶₂ σs₂ ↑✶₂ k) → 
                            ∀ k t → t /✶₁ σs₁ ↑✶₁ k ≡ t /✶₂ σs₂ ↑✶₂ k
        /✶-↑✶ ρs₁ ρs₂ hyp k (simpl (tvar x)) = hyp k x
        /✶-↑✶ ρs₁ ρs₂ hyp k (simpl (tc c)) = begin
            (simpl $ tc c) /✶₁ ρs₁ ↑✶₁ k
            ≡⟨ TypeApp.tc-/✶-↑✶ _ k ρs₁ ⟩
            (simpl $ tc c)
            ≡⟨ sym $ TypeApp.tc-/✶-↑✶ _ k ρs₂ ⟩
            (simpl $ tc c) /✶₂ ρs₂ ↑✶₂ k ∎
        /✶-↑✶ ρs₁ ρs₂ hyp k (simpl (a →' b)) = begin
            (simpl $ a →' b) /✶₁ ρs₁ ↑✶₁ k
            ≡⟨ TypeApp.→'-/✶-↑✶ _ k ρs₁ ⟩
            simpl ((a /✶₁ ρs₁ ↑✶₁ k) →' (b /✶₁ ρs₁ ↑✶₁ k))
            ≡⟨ cong₂ (λ a b → simpl (a →' b)) (/✶-↑✶ ρs₁ ρs₂ hyp k a) (/✶-↑✶ ρs₁ ρs₂ hyp k b) ⟩
            simpl ((a /✶₂ ρs₂ ↑✶₂ k) →' (b /✶₂ ρs₂ ↑✶₂ k))
            ≡⟨ sym (TypeApp.→'-/✶-↑✶ _ k ρs₂) ⟩
            (simpl $ a →' b) /✶₂ ρs₂ ↑✶₂ k
            ∎
        /✶-↑✶ ρs₁ ρs₂ hyp k (a ⇒ b) = begin
            (a ⇒ b) /✶₁ ρs₁ ↑✶₁ k
            ≡⟨ TypeApp.⇒-/✶-↑✶ _ k ρs₁ ⟩ -- 
            (a /✶₁ ρs₁ ↑✶₁ k) ⇒ (b /✶₁ ρs₁ ↑✶₁ k)
            ≡⟨ cong₂ _⇒_ (/✶-↑✶ ρs₁ ρs₂ hyp k a) (/✶-↑✶ ρs₁ ρs₂ hyp k b) ⟩
            (a /✶₂ ρs₂ ↑✶₂ k) ⇒ (b /✶₂ ρs₂ ↑✶₂ k)
            ≡⟨ sym (TypeApp.⇒-/✶-↑✶ _ k ρs₂) ⟩
            (a ⇒ b) /✶₂ ρs₂ ↑✶₂ k
            ∎
        /✶-↑✶ ρs₁ ρs₂ hyp k (∀' a) = begin
            (∀' a) /✶₁ ρs₁ ↑✶₁ k
            ≡⟨ TypeApp.∀'-/✶-↑✶ _ k ρs₁ ⟩
            ∀' (a /✶₁ ρs₁ ↑✶₁ (suc k))
            ≡⟨ cong ∀' (/✶-↑✶ ρs₁ ρs₂ hyp (suc k) a) ⟩
            ∀' (a /✶₂ ρs₂ ↑✶₂ (suc k))
            ≡⟨ sym (TypeApp.∀'-/✶-↑✶ _ k ρs₂) ⟩
            (∀' a) /✶₂ ρs₂ ↑✶₂ k
            ∎

  open TermLemmas typeLemmas public hiding (var; id; _/_)
  open AdditionalLemmas typeLemmas public

  -- The above lemma /✶-↑✶ specialized to single substitutions
  /-↑⋆ : ∀ {T₁ T₂} {lift₁ : Lift T₁ Type} {lift₂ : Lift T₂ Type} →
      let open Lifted lift₁ using () renaming (_↑⋆_ to _↑⋆₁_; _/_ to _/₁_)
          open Lifted lift₂ using () renaming (_↑⋆_ to _↑⋆₂_; _/_ to _/₂_)
      in
      ∀ {n k} (ρ₁ : Sub T₁ n k) (ρ₂ : Sub T₂ n k) →
      (∀ i x → (simpl (tvar x)) /₁ ρ₁ ↑⋆₁ i ≡ (simpl (tvar x)) /₂ ρ₂ ↑⋆₂ i) →
          ∀ i a → a /₁ ρ₁ ↑⋆₁ i ≡ a /₂ ρ₂ ↑⋆₂ i
  /-↑⋆ ρ₁ ρ₂ hyp i a = /✶-↑✶ (ρ₁ ◅ ε) (ρ₂ ◅ ε) hyp i a

module MetaTypeTypeLemmas where
  open MetaTypeTypeSubst hiding (_/✶_)
  open import Implicits.Oliveira.Types.Unification.Types TC _tc≟_
  open import Data.Star

  private module V = VarLemmas

  module _ {m : ℕ} where

    MT : ℕ → Set
    MT = MetaType m

    open MetaTypeApp hiding (_/_)

    module _ {T₁ T₂} {lift₁ : MetaLift T₁} {lift₂ : MetaLift T₂} where

        open Lifted {m} lift₁ using () renaming (_↑✶_ to _↑✶₁_; _/✶_ to _/✶₁_)
        open Lifted {m} lift₂ using () renaming (_↑✶_ to _↑✶₂_; _/✶_ to _/✶₂_)

        /✶-↑✶ : ∀ {n n'} (ρs₁ : Subs (T₁ m) n n') (ρs₂ : Subs (T₂ m) n n') →
                (∀ k x → (simpl (tvar x)) /✶₁ ρs₁ ↑✶₁ k ≡ (simpl (tvar x)) /✶₂ ρs₂ ↑✶₂ k) → 
                ∀ k t → t /✶₁ ρs₁ ↑✶₁ k ≡ t /✶₂ ρs₂ ↑✶₂ k
        /✶-↑✶ ρs₁ ρs₂ hyp k (a ⇒ b) = begin
                (a ⇒ b) /✶₁ ρs₁ ↑✶₁ k
            ≡⟨ ⇒-/✶-↑✶ lift₁ k ρs₁ ⟩
                ((a /✶₁ ρs₁ ↑✶₁ k) ⇒ (b /✶₁ ρs₁ ↑✶₁ k))
            ≡⟨ cong₂ _⇒_ (/✶-↑✶ ρs₁ ρs₂ hyp k a) (/✶-↑✶ ρs₁ ρs₂ hyp k b) ⟩
                (a /✶₂ ρs₂ ↑✶₂ k) ⇒ (b /✶₂ ρs₂ ↑✶₂ k)
            ≡⟨ sym (⇒-/✶-↑✶ lift₂ k ρs₂) ⟩
                (a ⇒ b) /✶₂ ρs₂ ↑✶₂ k ∎
        /✶-↑✶ ρs₁ ρs₂ hyp k (∀' t) = begin
                (∀' t) /✶₁ ρs₁ ↑✶₁ k
            ≡⟨ ∀'-/✶-↑✶ lift₁ k ρs₁ ⟩
                ∀' (t /✶₁ ρs₁ ↑✶₁ (suc k))
            ≡⟨ cong ∀' (/✶-↑✶ ρs₁ ρs₂ hyp (suc k) t) ⟩
                ∀' (t /✶₂ ρs₂ ↑✶₂ (suc k))
            ≡⟨ sym $ ∀'-/✶-↑✶ lift₂ k ρs₂ ⟩
                (∀' t) /✶₂ ρs₂ ↑✶₂ k ∎
        /✶-↑✶ ρs₁ ρs₂ hyp k (simpl (tvar c)) = hyp k c
        /✶-↑✶ ρs₁ ρs₂ hyp k (simpl (mvar x)) = begin
                (simpl (mvar x)) /✶₁ ρs₁ ↑✶₁ k
            ≡⟨ mvar-/✶-↑✶ lift₁ k ρs₁ ⟩
                (simpl (mvar x))
            ≡⟨ sym $ mvar-/✶-↑✶ lift₂ k ρs₂ ⟩
                (simpl (mvar x)) /✶₂ ρs₂ ↑✶₂ k ∎
        /✶-↑✶ ρs₁ ρs₂ hyp k (simpl (a →' b)) = begin
                (simpl (a →' b)) /✶₁ ρs₁ ↑✶₁ k
            ≡⟨ →'-/✶-↑✶ lift₁ k ρs₁ ⟩
                simpl ((a /✶₁ ρs₁ ↑✶₁ k) →' (b /✶₁ ρs₁ ↑✶₁ k))
            ≡⟨ cong₂ (λ a b → simpl (a →' b)) (/✶-↑✶ ρs₁ ρs₂ hyp k a) (/✶-↑✶ ρs₁ ρs₂ hyp k b) ⟩
                simpl ((a /✶₂ ρs₂ ↑✶₂ k) →' (b /✶₂ ρs₂ ↑✶₂ k))
            ≡⟨ sym (→'-/✶-↑✶ lift₂ k ρs₂) ⟩
                (simpl (a →' b)) /✶₂ ρs₂ ↑✶₂ k ∎
        /✶-↑✶ ρs₁ ρs₂ hyp k (simpl (tc c)) = begin
                (simpl (tc c)) /✶₁ ρs₁ ↑✶₁ k
            ≡⟨ tc-/✶-↑✶ lift₁ k ρs₁ ⟩
                (simpl (tc c))
            ≡⟨ sym $ tc-/✶-↑✶ lift₂ k ρs₂ ⟩
                (simpl (tc c)) /✶₂ ρs₂ ↑✶₂ k ∎

    lemmas₃ : Lemmas₃ (MetaType m)
    lemmas₃ = record
        { lemmas₂ = record
        { lemmas₁ = record
            { lemmas₀ = record
            { simple = simple
            }
            ; weaken-var = λ {_ x} → begin
                (simpl (tvar x)) /Var V.wk      ≡⟨ refl ⟩
                (simpl (tvar (lookup x V.wk)))  ≡⟨ cong (λ x → simpl (tvar x)) (V.lookup-wk x) ⟩
                (simpl (tvar (suc x)))          ∎
            }
        ; application = Subst.application subst
        ; var-/       = refl
        }
        ; /✶-↑✶ = /✶-↑✶
        }

    private module L₃ = Lemmas₃ lemmas₃

    lemmas₅ : Lemmas₅ (MetaType m)
    lemmas₅ = record
        { lemmas₄ = record
        { lemmas₃ = lemmas₃
        ; /-wk    = λ {_ t} → begin
            t / wk       ≡⟨ /✶-↑✶ (ε ▻ wk) (ε ▻ V.wk)
                                (λ k x → begin
                                (simpl (tvar x)) / wk ↑⋆ k
                                  ≡⟨ L₃.var-/-wk-↑⋆ k x ⟩
                                (simpl (tvar (finlift k suc x)))
                                  ≡⟨ cong (λ x → (simpl (tvar x))) (sym (V.var-/-wk-↑⋆ k x)) ⟩
                                (simpl (tvar (lookup x (V._↑⋆_ V.wk k))))
                                  ≡⟨ refl ⟩
                                (simpl (tvar x)) /Var V._↑⋆_ V.wk k        ∎)
                                zero t ⟩
            t /Var V.wk  ≡⟨ refl ⟩
            weaken t     ∎
        }
        }

    open Lemmas₅ lemmas₅ public hiding (lemmas₃)

module MetaTypeMetaLemmas' where
  open MetaTypeMetaSubst using (module Lifted; MetaLift)
  open import Implicits.Oliveira.Types.Unification.Types TC _tc≟_
  open import Data.Star as Star
  open import Data.Star.Properties

  private module V = VarLemmas

  module MetaTypeAppLemmas {T} (l : MetaLift T) where
    open Lifted l

    →'-/✶-↑✶ : ∀ k {ν n n' a b} (ρs : Subs (flip T ν) n n') →
            (simpl (a →' b)) /✶ ρs ↑✶ k ≡ simpl ((a /✶ ρs ↑✶ k) →' (b /✶ ρs ↑✶ k))
    →'-/✶-↑✶ k ε        = refl
    →'-/✶-↑✶ k (r ◅ ρs) = cong₂ _/_ (→'-/✶-↑✶ k ρs) refl

    ⇒-/✶-↑✶ : ∀ k {ν n n' a b} (ρs : Subs (flip T ν) n n') →
            (a ⇒ b) /✶ ρs ↑✶ k ≡ (a /✶ ρs ↑✶ k) ⇒ (b /✶ ρs ↑✶ k)
    ⇒-/✶-↑✶ k ε        = refl
    ⇒-/✶-↑✶ k (r ◅ ρs) = cong₂ _/_ (⇒-/✶-↑✶ k ρs) refl

    tc-/✶-↑✶ : ∀ k {ν c n n'} (ρs : Subs (flip T ν) n n') →
            (simpl (tc c)) /✶ ρs ↑✶ k ≡ simpl (tc c)
    tc-/✶-↑✶ k ε        = refl
    tc-/✶-↑✶ k (r ◅ ρs) = cong₂ _/_ (tc-/✶-↑✶ k ρs) refl 

    tvar-/✶-↑✶ : ∀ k {ν n n' c} (ρs : Subs (flip T ν) n n') →
            (simpl (tvar c)) /✶ ρs ↑✶ k ≡ simpl (tvar c)
    tvar-/✶-↑✶ k ε        = refl
    tvar-/✶-↑✶ k (r ◅ ρs) = cong₂ _/_ (tvar-/✶-↑✶ k ρs) refl 

    tpweaken-subs : ∀ {ν n n'} (ρs : Subs (flip T ν) n n') → Subs (flip T (suc ν)) n n'
    tpweaken-subs ρs = Star.map (λ x → x ↑tp) ρs

    mutual
      comm-↑⋆-↑tp : ∀ k {ν n n'} (s : Sub (flip T ν) n n') → (s ↑⋆ k) ↑tp ≡ (s ↑tp) ↑⋆ k
      comm-↑⋆-↑tp zero s = refl
      comm-↑⋆-↑tp (suc k) s = begin
        ((s ↑⋆ k) ↑) ↑tp
          ≡⟨ comm-↑-↑tp (s ↑⋆ k) ⟩
        ((s ↑⋆ k) ↑tp) ↑
          ≡⟨ cong _↑ (comm-↑⋆-↑tp k s) ⟩
        (s ↑tp) ↑⋆ (suc k) ∎

    comm-tpweaken-↑✶ : ∀ k {ν n n'} (ρs : Subs (flip T ν) n n') →
                     (tpweaken-subs ρs) ↑✶ k ≡ tpweaken-subs (ρs ↑✶ k)
    comm-tpweaken-↑✶ k ρs = begin
       (tpweaken-subs ρs) ↑✶ k
         ≡⟨ refl ⟩
       Star.gmap (_N+_ k) (λ ρ → ρ ↑⋆ k) (Star.map _↑tp ρs)
         ≡⟨ gmap-∘ (_N+_ k) (λ ρ₁ → ρ₁ ↑⋆ k) Prelude.id _↑tp ρs ⟩
       Star.gmap (_N+_ k) (λ ρ → (ρ ↑tp) ↑⋆ k) ρs
       ≡⟨ gmap-cong (_N+_ k) (λ ρ₁ → _↑tp ρ₁ ↑⋆ k) (λ ρ₁ → _↑tp (ρ₁ ↑⋆ k))
           (λ s → sym $ comm-↑⋆-↑tp k s) ρs ⟩
       Star.gmap (_N+_ k) (λ ρ → (ρ ↑⋆ k) ↑tp) ρs
         ≡⟨ sym $ gmap-∘ Prelude.id _↑tp (_N+_ k) (λ ρ₁ → ρ₁ ↑⋆ k) ρs ⟩
       Star.map _↑tp (Star.gmap (_N+_ k) (λ ρ → ρ ↑⋆ k) ρs)
         ≡⟨ refl ⟩
       tpweaken-subs (ρs ↑✶ k) ∎

    ∀'-/✶-↑✶ : ∀ k {ν n n' a} (ρs : Subs (flip T ν) n n') →
               (∀' a) /✶ ρs ↑✶ k ≡ ∀' (a /✶ (tpweaken-subs ρs) ↑✶ k)
    ∀'-/✶-↑✶ k {a = a} ε = refl
    ∀'-/✶-↑✶ k {a = a} (x ◅ ρs) = begin
        (∀' a) /✶ (x  ◅ ρs) ↑✶ k 
          ≡⟨ cong (flip _/_ (x ↑⋆ k)) (∀'-/✶-↑✶ k ρs) ⟩
        (∀' (a /✶ (tpweaken-subs ρs) ↑✶ k)) / (x ↑⋆ k)
          ≡⟨ cong (λ u → ∀' (a /✶ u / _↑tp (x ↑⋆ k))) (comm-tpweaken-↑✶ k ρs) ⟩
        ∀' (a /✶ (tpweaken-subs ((x ◅ ρs) ↑✶ k)))
          ≡⟨ sym $ cong (λ u → ∀' (a /✶ u)) (comm-tpweaken-↑✶ k (x ◅ ρs)) ⟩
        ∀' (a /✶ (tpweaken-subs (x ◅ ρs)) ↑✶ k) ∎

  module _ {T₁ T₂} {lift₁ : MetaLift T₁} {lift₂ : MetaLift T₂} where

    open Lifted lift₁ using () renaming (_↑✶_ to _↑✶₁_; _/✶_ to _/✶₁_)
    open Lifted lift₂ using () renaming (_↑✶_ to _↑✶₂_; _/✶_ to _/✶₂_)

    open MetaTypeAppLemmas

    postulate letstry : ∀ {ν n n'} (ρs₁ : Subs (flip T₁ ν) n n') (ρs₂ : Subs (flip T₂ ν) n n') →
                        (∀ k x → (simpl (mvar x)) /✶₁ ρs₁ ↑✶₁ k ≡ (simpl (mvar x)) /✶₂ ρs₂ ↑✶₂ k) →  
                        (∀ k x → (simpl (mvar x)) /✶₁ (tpweaken-subs lift₁ ρs₁) ↑✶₁ k ≡ (simpl (mvar x)) /✶₂ (tpweaken-subs lift₂ ρs₂) ↑✶₂ k)
    -- letstry ρs₁ ρs₂ hyp k x = {!!}

    /✶-↑✶ : ∀ {ν n n'} (ρs₁ : Subs (flip T₁ ν) n n') (ρs₂ : Subs (flip T₂ ν) n n') →
            (∀ k x → (simpl (mvar x)) /✶₁ ρs₁ ↑✶₁ k ≡ (simpl (mvar x)) /✶₂ ρs₂ ↑✶₂ k) → 
            ∀ k t → t /✶₁ ρs₁ ↑✶₁ k ≡ t /✶₂ ρs₂ ↑✶₂ k
    /✶-↑✶ ρs₁ ρs₂ hyp k (a ⇒ b) = begin
            (a ⇒ b) /✶₁ ρs₁ ↑✶₁ k
        ≡⟨ ⇒-/✶-↑✶ lift₁ k ρs₁ ⟩
            ((a /✶₁ ρs₁ ↑✶₁ k) ⇒ (b /✶₁ ρs₁ ↑✶₁ k))
        ≡⟨ cong₂ _⇒_ (/✶-↑✶ ρs₁ ρs₂ hyp k a) (/✶-↑✶ ρs₁ ρs₂ hyp k b) ⟩
            (a /✶₂ ρs₂ ↑✶₂ k) ⇒ (b /✶₂ ρs₂ ↑✶₂ k)
        ≡⟨ sym (⇒-/✶-↑✶ lift₂ k ρs₂) ⟩
            (a ⇒ b) /✶₂ ρs₂ ↑✶₂ k ∎
    /✶-↑✶ ρs₁ ρs₂ hyp k (∀' t) = begin
            (∀' t) /✶₁ ρs₁ ↑✶₁ k
        ≡⟨ ∀'-/✶-↑✶ lift₁ k ρs₁ ⟩
            (∀' (t /✶₁ (tpweaken-subs lift₁ ρs₁) ↑✶₁ k))
        ≡⟨ cong ∀' (/✶-↑✶ (tpweaken-subs lift₁ ρs₁) (tpweaken-subs lift₂ ρs₂) (letstry ρs₁ ρs₂ hyp) k t ) ⟩
            (∀' (t /✶₂ (tpweaken-subs lift₂ ρs₂) ↑✶₂ k))
        ≡⟨ sym $ ∀'-/✶-↑✶ lift₂ k ρs₂ ⟩
            (∀' t) /✶₂ ρs₂ ↑✶₂ k ∎
    /✶-↑✶ ρs₁ ρs₂ hyp k (simpl (mvar c)) = hyp k c
    /✶-↑✶ ρs₁ ρs₂ hyp k (simpl (tvar x)) = begin
            (simpl (tvar x)) /✶₁ ρs₁ ↑✶₁ k
        ≡⟨ tvar-/✶-↑✶ lift₁ k ρs₁ ⟩
            (simpl (tvar x))
        ≡⟨ sym $ tvar-/✶-↑✶ lift₂ k ρs₂ ⟩
            (simpl (tvar x)) /✶₂ ρs₂ ↑✶₂ k ∎
    /✶-↑✶ ρs₁ ρs₂ hyp k (simpl (a →' b)) = begin
            (simpl (a →' b)) /✶₁ ρs₁ ↑✶₁ k
        ≡⟨ →'-/✶-↑✶ lift₁ k ρs₁ ⟩
            simpl ((a /✶₁ ρs₁ ↑✶₁ k) →' (b /✶₁ ρs₁ ↑✶₁ k))
        ≡⟨ cong₂ (λ a b → simpl (a →' b)) (/✶-↑✶ ρs₁ ρs₂ hyp k a) (/✶-↑✶ ρs₁ ρs₂ hyp k b) ⟩
            simpl ((a /✶₂ ρs₂ ↑✶₂ k) →' (b /✶₂ ρs₂ ↑✶₂ k))
        ≡⟨ sym (→'-/✶-↑✶ lift₂ k ρs₂) ⟩
            (simpl (a →' b)) /✶₂ ρs₂ ↑✶₂ k ∎
    /✶-↑✶ ρs₁ ρs₂ hyp k (simpl (tc c)) = begin
            (simpl (tc c)) /✶₁ ρs₁ ↑✶₁ k
        ≡⟨ tc-/✶-↑✶ lift₁ k ρs₁ ⟩
            (simpl (tc c))
        ≡⟨ sym $ tc-/✶-↑✶ lift₂ k ρs₂ ⟩
            (simpl (tc c)) /✶₂ ρs₂ ↑✶₂ k ∎

  module _ {ν : ℕ} where
    open MetaTypeMetaSubst

    MT : ℕ → Set
    MT = flip MetaType ν

    lemmas₃ : Lemmas₃ (flip MetaType ν)
    lemmas₃ = record
        { lemmas₂ = record
        { lemmas₁ = record
            { lemmas₀ = record
            { simple = simple
            }
            ; weaken-var = λ {_ x} → begin
                (simpl (mvar x)) /Var V.wk      ≡⟨ refl ⟩
                (simpl (mvar (lookup x V.wk)))  ≡⟨ cong (λ x → simpl (mvar x)) (V.lookup-wk x) ⟩
                (simpl (mvar (suc x)))          ∎
            }
        ; application = Subst.application subst
        ; var-/       = refl
        }
        ; /✶-↑✶ = /✶-↑✶
        }

    private module L₃ = Lemmas₃ lemmas₃

    lemmas₅ : Lemmas₅ (flip MetaType ν)
    lemmas₅ = record
        { lemmas₄ = record
        { lemmas₃ = lemmas₃
        ; /-wk    = λ {_ t} → begin
            t / wk       ≡⟨ /✶-↑✶ (ε ▻ wk) (ε ▻ V.wk)
                                (λ k x → begin
                                (simpl (mvar x)) / wk ↑⋆ k
                                  ≡⟨ L₃.var-/-wk-↑⋆ k x ⟩
                                (simpl (mvar (finlift k suc x)))
                                  ≡⟨ cong (λ x → (simpl (mvar x))) (sym (V.var-/-wk-↑⋆ k x)) ⟩
                                (simpl (mvar (lookup x (V._↑⋆_ V.wk k))))
                                  ≡⟨ refl ⟩
                                (simpl (mvar x)) /Var V._↑⋆_ V.wk k        ∎)
                                zero t ⟩
            t /Var V.wk  ≡⟨ refl ⟩
            weaken t     ∎
        }
        }

    open Lemmas₅ lemmas₅ public hiding (lemmas₃)

{-}
module MetaTypeMetaLemmas where
  open MetaTypeMetaSubst 
  open import Implicits.Oliveira.Types.Unification.Types TC _tc≟_

  module ExpandSimple {ν : ℕ} where
    private module V = VarLemmas

    lemmas₂ : Lemmas₂ (flip MetaType ν)
    lemmas₂ = record
        { lemmas₁ = record
            { lemmas₀ = record { simple = simple {ν}}
            ; weaken-var = λ {_ x} → begin
                (simpl (mvar x)) /Var V.wk      ≡⟨ refl ⟩
                (simpl (mvar (lookup x V.wk)))  ≡⟨ cong (λ n → simpl (mvar n)) (V.lookup-wk x) ⟩
                (simpl (mvar (suc x)))          ∎
            }
        ; application = Subst.application subst
        ; var-/       = refl }

    open Lemmas₂ lemmas₂ public

  module Expand₃ {ν : ℕ} where
    
    MT = (flip MetaType ν)
    open import Data.Star

    →'-/✶-↑✶ : ∀ k {m n a b} (ρs : Subs MT m n) →
               (simpl (a →' b)) /✶ ρs ↑✶ k ≡ simpl ((a /✶ ρs ↑✶ k) →' (b /✶ ρs ↑✶ k))
    →'-/✶-↑✶ k ε        = refl
    →'-/✶-↑✶ k (r ◅ ρs) = cong₂ _/_ (→'-/✶-↑✶ k ρs) refl

    ⇒-/✶-↑✶ : ∀ k {m n a b} (ρs : Subs MT m n) →
               (a ⇒ b) /✶ ρs ↑✶ k ≡ (a /✶ ρs ↑✶ k) ⇒ (b /✶ ρs ↑✶ k)
    ⇒-/✶-↑✶ k ε        = refl
    ⇒-/✶-↑✶ k (r ◅ ρs) = cong₂ _/_ (⇒-/✶-↑✶ k ρs) refl

    tc-/✶-↑✶ : ∀ k {c m n} (ρs : Subs MT m n) →
               (simpl (tc c)) /✶ ρs ↑✶ k ≡ simpl (tc c)
    tc-/✶-↑✶ k ε        = refl
    tc-/✶-↑✶ k (r ◅ ρs) = cong₂ _/_ (tc-/✶-↑✶ k ρs) refl 

    tvar-/✶-↑✶ : ∀ k {c m n} (ρs : Subs MT m n) →
               (simpl (tvar c)) /✶ ρs ↑✶ k ≡ simpl (tvar c)
    tvar-/✶-↑✶ k ε        = refl
    tvar-/✶-↑✶ k (r ◅ ρs) = cong₂ _/_ (tvar-/✶-↑✶ k ρs) refl 

    postulate ∀'-/✶-↑✶ : ∀ {m n} (ρs₁ ρs₂ : Subs MT m n) →
                        (∀ k x → (simpl (mvar x)) /✶ ρs₁ ↑✶ k ≡ (simpl (mvar x)) /✶ ρs₂ ↑✶ k) →
                        ∀ k t → (∀' t) /✶ ρs₁ ↑✶ k ≡ (∀' t) /✶ ρs₂ ↑✶ k

    /✶-↑✶ : ∀ {m n} (ρs₁ ρs₂ : Subs MT m n) →
            (∀ k x → (simpl (mvar x)) /✶ ρs₁ ↑✶ k ≡ (simpl (mvar x)) /✶ ρs₂ ↑✶ k) →
            ∀ k t → t /✶ ρs₁ ↑✶ k ≡ t /✶ ρs₂ ↑✶ k
    /✶-↑✶ ρs₁ ρs₂ hyp k (a ⇒ b) = begin
            (a ⇒ b) /✶ ρs₁ ↑✶ k
         ≡⟨ ⇒-/✶-↑✶ k ρs₁ ⟩
            ((a /✶ ρs₁ ↑✶ k) ⇒ (b /✶ ρs₁ ↑✶ k))
         ≡⟨ cong₂ _⇒_ (/✶-↑✶ ρs₁ ρs₂ hyp k a) (/✶-↑✶ ρs₁ ρs₂ hyp k b) ⟩
            (a /✶ ρs₂ ↑✶ k) ⇒ (b /✶ ρs₂ ↑✶ k)
         ≡⟨ sym (⇒-/✶-↑✶ k ρs₂) ⟩
            (a ⇒ b) /✶ ρs₂ ↑✶ k ∎
    /✶-↑✶ ρs₁ ρs₂ hyp k (∀' t) = ∀'-/✶-↑✶ ρs₁ ρs₂ hyp k t
      
    /✶-↑✶ ρs₁ ρs₂ hyp k (simpl (tvar c)) = begin
            (simpl (tvar c)) /✶ ρs₁ ↑✶ k
          ≡⟨ tvar-/✶-↑✶ k ρs₁ ⟩
            (simpl (tvar c))
          ≡⟨ sym $ tvar-/✶-↑✶ k ρs₂ ⟩
            (simpl (tvar c)) /✶ ρs₂ ↑✶ k ∎
    /✶-↑✶ ρs₁ ρs₂ hyp k (simpl (mvar x)) = hyp k x
    /✶-↑✶ ρs₁ ρs₂ hyp k (simpl (a →' b)) = begin
            (simpl (a →' b)) /✶ ρs₁ ↑✶ k
         ≡⟨ →'-/✶-↑✶ k ρs₁ ⟩
            simpl ((a /✶ ρs₁ ↑✶ k) →' (b /✶ ρs₁ ↑✶ k))
         ≡⟨ cong₂ (λ a b → simpl (a →' b)) (/✶-↑✶ ρs₁ ρs₂ hyp k a) (/✶-↑✶ ρs₁ ρs₂ hyp k b) ⟩
            simpl ((a /✶ ρs₂ ↑✶ k) →' (b /✶ ρs₂ ↑✶ k))
         ≡⟨ sym (→'-/✶-↑✶ k ρs₂) ⟩
            (simpl (a →' b)) /✶ ρs₂ ↑✶ k ∎
    /✶-↑✶ ρs₁ ρs₂ hyp k (simpl (tc c)) = begin
            (simpl (tc c)) /✶ ρs₁ ↑✶ k
          ≡⟨ tc-/✶-↑✶ k ρs₁ ⟩
            (simpl (tc c))
          ≡⟨ sym $ tc-/✶-↑✶ k ρs₂ ⟩
            (simpl (tc c)) /✶ ρs₂ ↑✶ k ∎

    lemmas₃ : Lemmas₃ (flip MetaType ν)
    lemmas₃ = record {
        lemmas₂ = ExpandSimple.lemmas₂;
        /✶-↑✶ = /✶-↑✶ }

    open Lemmas₃ lemmas₃ public hiding (/✶-↑✶)

  us↑-⊙-sub-u≡u∷us : ∀ {ν} u (us : MetaSub MetaType ν zero zero) → us ↑ ⊙ sub u ≡ u ∷ us
  us↑-⊙-sub-u≡u∷us {ν} u us = begin
    (u ∷ (map (λ t → t / wk ⊙ (sub u)) us))
      ≡⟨ cong (λ v → u ∷ v) (map-cong (λ x → cong (_/_ x) (ExpandSimple.wk-⊙-sub {t = x})) us) ⟩
    (u ∷ (map (λ t → t / id) us))
      ≡⟨ cong (λ v → u ∷ v) (map-cong Expand₃.id-vanishes us) ⟩
    (u ∷ (map Prelude.id us))
      ≡⟨ cong (_∷_ u) (map-id us) ⟩
    u ∷ us ∎

  {-}
  open-mvar : ∀ {ν m} (x : Fin m) → open-meta {ν = ν} (simpl (mvar x)) ≡ simpl (mvar (suc x))
  open-mvar x = begin
    open-meta (simpl (mvar x))
      ≡⟨ refl ⟩
    (weaken (simpl (mvar x))) MetaTypeTypeSubst./ (sub (simpl (mvar zero)))
      ≡⟨ {!!} ⟩
    ((simpl (mvar x)) / wk) MetaTypeTypeSubst./ (sub (simpl (mvar zero)))
      ≡⟨ {!!} ⟩
    simpl (mvar (suc x)) ∎
  
  lem : ∀ {ν} (a : MetaType zero (suc ν)) (u : MetaType zero ν) →
        (from-meta a) tp[/tp from-meta u ] ≡ from-meta ((open-meta a) / (sub u))
  lem (a ⇒ b) u = {!!}
  lem (∀' a) u = {!!}
  lem (simpl (tvar x)) u = {!!}
  lem (simpl (mvar x)) u = begin
    (from-meta (simpl (mvar x))) tp[/tp from-meta u ]
      ≡⟨ {!!} ⟩
    (from-meta ((simpl (mvar (suc x))) / (sub u)))
      ≡⟨ {!!} ⟩
    (from-meta ((open-meta (simpl (mvar x))) / (sub u))) ∎
  lem (simpl (a →' b)) u = {!!}
  lem (simpl (tc c)) u = refl
  -}

  open Expand₃ public
-}

module SubstLemmas (_⊢ᵣ_ : ∀ {ν n} → Ktx ν n → Type ν → Set) where

  open TypingRules _⊢ᵣ_

  private
    ⊢subst : ∀ {m n} {Γ₁ Γ₂ : Ktx n m} {t₁ t₂ : Term n m} {a₁ a₂ : Type n} →
      Γ₁ ≡ Γ₂ → t₁ ≡ t₂ → a₁ ≡ a₂ → Γ₁ ⊢ t₁ ∈ a₁ → Γ₂ ⊢ t₂ ∈ a₂
    ⊢subst refl refl refl hyp = hyp
  
    ⊢substCtx : ∀ {m n} {Γ₁ Γ₂ : Ktx n m} {t : Term n m} {a : Type n} →
      Γ₁ ≡ Γ₂ → Γ₁ ⊢ t ∈ a → Γ₂ ⊢ t ∈ a
    ⊢substCtx refl hyp = hyp
  
    ⊢substTp : ∀ {m n} {Γ : Ktx n m} {t : Term n m} {a₁ a₂ : Type n} →
      a₁ ≡ a₂ → Γ ⊢ t ∈ a₁ → Γ ⊢ t ∈ a₂
    ⊢substTp refl hyp = hyp 
  
  module WtTermLemmas where
    postulate weaken : ∀ {ν n} {K : Ktx ν n} {t : Term ν n} {a b : Type ν} →
                       K ⊢ t ∈ a → b ∷Γ K ⊢ tmtm-weaken t ∈ a
    -- weaken {Γ = Γ} {b = b} ⊢t = Var.wk /Var ⊢substCtx (C.wkVar-/Var-∷ Γ b) ⊢t
  
  {-
  module TermTypeLemmas where
    open TermTypeSubst 
  
    private module T = TypeLemmas
    private module TS = TypeSubst
    private module V = VarLemmas
  
    /-↑⋆ :
      ∀ {T₁ T₂} {lift₁ : Lift T₁ Type} {lift₂ : Lift T₂ Type} →
      let open TS.Lifted lift₁ using () renaming (_↑⋆_ to _↑⋆₁_; _/_ to _/tp₁_)
          open   Lifted lift₁ using () renaming (_/_  to _/₁_)
          open TS.Lifted lift₂ using () renaming (_↑⋆_ to _↑⋆₂_; _/_ to _/tp₂_)
          open   Lifted lift₂ using () renaming (_/_  to _/₂_)
      in
      ∀ {n k} (ρ₁ : Sub T₁ n k) (ρ₂ : Sub T₂ n k) →
      (∀ i x → tvar x /tp₁ ρ₁ ↑⋆₁ i ≡ tvar x /tp₂ ρ₂ ↑⋆₂ i) →
       ∀ i {m} (t : Term (i N+ n) m)  → t /₁ ρ₁ ↑⋆₁ i ≡ t /₂ ρ₂ ↑⋆₂ i
    /-↑⋆ ρ₁ ρ₂ hyp i (new x)      = refl
    /-↑⋆ ρ₁ ρ₂ hyp i (var x)      = refl
    /-↑⋆ ρ₁ ρ₂ hyp i (Λ t)        = cong Λ      (/-↑⋆ ρ₁ ρ₂ hyp (1 N+ i) t)
    /-↑⋆ ρ₁ ρ₂ hyp i (λ' a t)     =
      cong₂ λ'     (T./-↑⋆ ρ₁ ρ₂ hyp i a)       (/-↑⋆ ρ₁ ρ₂ hyp i t)
    /-↑⋆ ρ₁ ρ₂ hyp i (t [ b ])    =
      cong₂ _[_]     (/-↑⋆ ρ₁ ρ₂ hyp i t)     (T./-↑⋆ ρ₁ ρ₂ hyp i b)
    /-↑⋆ ρ₁ ρ₂ hyp i (s · t)      =
      cong₂ _·_      (/-↑⋆ ρ₁ ρ₂ hyp i s)       (/-↑⋆ ρ₁ ρ₂ hyp i t)
    /-↑⋆ ρ₁ ρ₂ hyp i (x)      = {!!}
  
    /-wk : ∀ {m n} (t : Term m n) → t / TypeSubst.wk ≡ weaken t
    /-wk t = /-↑⋆ TypeSubst.wk VarSubst.wk (λ k x → begin
      tvar x T./ T.wk T.↑⋆ k ≡⟨ T.var-/-wk-↑⋆ k x ⟩
      tvar (finlift k suc x) ≡⟨ cong tvar (sym (V.var-/-wk-↑⋆ k x)) ⟩
      tvar (lookup x (V.wk V.↑⋆ k)) ≡⟨ refl ⟩
      tvar x TS./Var V.wk V.↑⋆ k ∎) 0 t
  
  module KtxLemmas where
    open KtxSubst hiding (ktx-map)
  
    private module Tp  = TypeLemmas
    private module Var = VarSubst
  
    ktx-map-cong : ∀ {ν μ n} {f g : Type ν → Type μ} →
                   f ≗ g → _≗_ {A = Ktx ν n} (ktx-map f) (ktx-map g)
    ktx-map-cong K = ?
  
    -- Term variable substitution (renaming) commutes with type
    -- substitution.
    {-
    /Var-/ : ∀ {m ν n l} (ρ : Sub Fin m n) (Γ : Ktx ν n) (σ : Sub Type ν l) →
             (Γ /Var ρ) / σ ≡ Γ /Var (ρ / σ)
    /Var-/ ρ Γ σ = begin
        (ρ /Var Γ) / σ
      ≡⟨ sym (map-∘ _ _ ρ) ⟩
        map (λ x → (lookup x Γ) Tp./ σ) ρ
      ≡⟨ map-cong (λ x → sym (Tp.lookup-⊙ x)) ρ ⟩
        map (λ x → lookup x (Γ / σ)) ρ
      ∎
  
    -- Term variable substitution (renaming) commutes with weakening of
    -- typing contexts with an additional type variable.
  
    /Var-weaken : ∀ {m n k} (ρ : Sub Fin m k) (Γ : Ctx n k) →
                  weaken (ρ /Var Γ) ≡ ρ /Var (weaken Γ)
    /Var-weaken ρ Γ = begin
      (ρ /Var Γ) / Tp.wk   ≡⟨ ? ⟩ --/Var-/ ρ Γ Tp.wk
      ρ /Var (weaken Γ)    ∎
      -}
  
    -- Term variable substitution (renaming) commutes with term variable
    -- lookup in typing context.
    {-
    /Var-lookup : ∀ {m n k} (x : Fin m) (ρ : Sub Fin m k) (Γ : Ctx n k) →
                  lookup x (ρ /Var Γ) ≡ lookup (lookup x ρ) Γ
    /Var-lookup x ρ Γ = op-<$> (lookup-morphism x) _ _
  
    -- Term variable substitution (renaming) commutes with weakening of
    -- typing contexts with an additional term variable.
    /Var-∷ : ∀ {m n k} (a : Type n) (ρ : Sub Fin m k) (Γ : Ctx n k) →
             a ∷ (ρ /Var Γ) ≡ (ρ Var.↑) /Var (a ∷ Γ)
    /Var-∷ a []      Γ = refl
    /Var-∷ a (x ∷ ρ) Γ = cong (_∷_ a) (cong (_∷_ (lookup x Γ)) (begin
      map (λ x → lookup x Γ) ρ                   ≡⟨ refl ⟩
      map (λ x → lookup (suc x) (a ∷ Γ)) ρ       ≡⟨ map-∘ _ _ ρ ⟩
      map (λ x → lookup x (a ∷ Γ)) (map suc ρ)   ∎))
  
    -- Invariants of term variable substitution (renaming)
    idVar-/Var   : ∀ {m n} (Γ : Ctx n m) → Γ ≡ (Var.id /Var Γ)
    wkVar-/Var-∷ : ∀ {m n} (Γ : Ctx n m) (a : Type n) → Γ ≡ (Var.wk /Var (a ∷ Γ))
  
    idVar-/Var []      = refl
    idVar-/Var (a ∷ Γ) = cong (_∷_ a) (wkVar-/Var-∷ Γ a)
  
    wkVar-/Var-∷ Γ a = begin
      Γ ≡⟨ idVar-/Var Γ ⟩
      Var.id /Var Γ ≡⟨ map-∘ _ _ VarSubst.id ⟩
      Var.wk /Var (a ∷ Γ) ∎
    
    ctx-weaken-sub-vanishes : ∀ {ν n} {Γ : Ktx ν n} {a} → (ktx-weaken Γ) / (Tp.sub a) ≡ Γ
    ctx-weaken-sub-vanishes {Γ = Γ} {a} = begin
      (Γ / Tp.wk) / (Tp.sub a) 
        ≡⟨ sym $ map-∘ (λ s → s tp/tp Tp.sub a) (λ s → s tp/tp Tp.wk) Γ ⟩
      (map (λ s → s tp/tp Tp.wk tp/tp (Tp.sub a)) Γ) 
        ≡⟨ map-cong (TypeLemmas.wk-sub-vanishes) Γ ⟩
      (map (λ s → s) Γ) ≡⟨ map-id Γ ⟩
      Γ ∎
    -}
  
  module WtTypeLemmas where
    open TypeLemmas hiding (_/_; weaken)
    private
      module Tp = TypeLemmas
      module TmTp = TermTypeLemmas
      module C  = KtxLemmas
  
    infixl 8 _/_
  
    -- Type substitutions lifted to well-typed terms
    _/_ : ∀ {m n k} {Γ : Ktx n m} {t : Term n m} {a : Type n} →
          Γ ⊢ t ∈ a → (σ : Sub Type n k) → Γ ktx/ σ ⊢ t tm/tp σ ∈ a Tp./ σ
    new c             / σ = new c
    var x             / σ = ⊢substTp (lookup-⊙ x) (var x)
    _/_ {Γ = Γ} (Λ ⊢t)  σ = Λ (⊢substCtx eq (⊢t / σ ↑))
      where
        postulate eq : (ktx-weaken Γ) ktx/ (σ Tp.↑) ≡ ktx-weaken (Γ ktx/ σ)
    {-
        eq = begin 
          (ktx-map (λ s → s tp/tp Tp.wk) Γ) ktx/ (σ Tp.↑) 
            ≡⟨ KtxLemmas.ktx-map-cong (λ a → a ktx/ (σ Tp.↑))
              (KtxLemmas.ktx-map-cong (λ a → Tp./-wk {t = a}) Γ) ⟩
          (ktx-map Tp.weaken Γ) ⊙ (σ Tp.↑) 
            ≡⟨ sym $ map-weaken-⊙ Γ σ ⟩
          map Tp.weaken (Γ ⊙ σ)
            ≡⟨ (map-cong (λ a → sym $ Tp./-wk {t = a}) (Γ ⊙ σ)) ⟩
          ktx-weaken (Γ ktx/ σ) ∎
          -}
    λ' a ⊢t           / σ = λ' (a Tp./ σ) (⊢t / σ)
    _[_] {a = a} ⊢t b / σ = ⊢substTp (sym (sub-commutes a)) ((⊢t / σ) [ b Tp./ σ ])
    ⊢s · ⊢t           / σ = (⊢s / σ) · (⊢t / σ)
    x / σ = ?
  
    -- Weakening of terms with additional type variables lifted to
    -- well-typed terms.
    weaken : ∀ {m n} {Γ : Ktx n m} {t : Term n m} {a : Type n} →
             Γ ⊢ t ∈ a → ktx-weaken Γ ⊢ tm-weaken t ∈ Tp.weaken a
    weaken {t = t} {a = a} ⊢t = ⊢subst refl (TmTp./-wk t) (/-wk {t = a}) (⊢t / wk)
  
    -- Weakening of terms with additional type variables lifted to
    -- collections of well-typed terms.
    weakenAll : ∀ {m n k} {Γ : Ktx n m} {ts : Vec (Term n m) k}
                  {as : Vec (Type n) k} → Γ ⊢ⁿ ts ∈ as →
                  ktx-weaken Γ ⊢ⁿ map tm-weaken ts ∈ map Tp.weaken as
    weakenAll {ts = []}    {[]}    []         = []
    weakenAll {ts = _ ∷ _} {_ ∷ _} (⊢t ∷ ⊢ts) = weaken ⊢t ∷ weakenAll ⊢ts
  
    -- Shorthand for single-variable type substitutions in well-typed
    -- terms.
    _[/_] : ∀ {m n} {Γ : Ktx (1 N+ n) m} {t a} →
            Γ ⊢ t ∈ a → (b : Type n) → Γ ktx/ sub b ⊢ t tm/tp sub b ∈ a Tp./ sub b
    ⊢t [/ b ] = ⊢t / sub b
  
    {-
    tm[/tp]-preserves : ∀ {ν n} {Γ : Ctx ν n} {t τ} → Γ ⊢ Λ t ∈ ∀' τ → ∀ a → Γ ⊢ (t tm[/tp a ]) ∈ τ tp[/tp a ]
    tm[/tp]-preserves {Γ = Γ} {t} {τ} (Λ p) a = ctx-subst C.ctx-weaken-sub-vanishes (p / (Tp.sub a))
      where
        ctx-subst = Prelude.subst (λ c → c ⊢ t tm[/tp a ] ∈ τ tp[/tp a ])
        -}
  
  module WtTermLemmas where
    private
      module Tp  = TypeLemmas
      module TmTp  = TermTypeLemmas
      module TmTm  = TermTermSubst
      module Var = VarSubst
      module C   = KtxLemmas
      TmSub = TmTm.TermSub Term
  
    infix 4 _⇒_⊢_
  
    -- Well-typed term substitutions are collections of well-typed terms.
    _⇒_⊢_ : ∀ {ν m k} → Ktx ν m → Ktx ν k → TmSub ν m k → Set
    Γ ⇒ Δ ⊢ s = Δ ⊢ⁿ s ∈ (proj₁ Γ)
  
    infixl 8  _/_ _/Var_
    infix  10 _↑
  
    -- Application of term variable substitutions (renaming) lifted to
    -- well-typed terms.
    _/Var_ : ∀ {ν m n} {K : Ktx ν n} {t : Term ν m} {a : Type ν}
               (s : Sub Fin m n) → s ktx/Var K ⊢ t ∈ a → K ⊢ t TmTm./Var s ∈ a
    _/Var_ {K = K} s (new c)   = new c
    _/Var_ {K = K} s (var x)   = ?
      -- ⊢substTp (sym (ktx/Var-lookup x ρ Γ)) (var (lookup x ρ))
    _/Var_ {K = K} s (Λ ⊢t)    = ?
      -- Λ    (ρ      /Var ⊢substCtx (ktx/Var-weaken ρ Γ) ⊢t)
    _/Var_ {K = K} s (λ' a ⊢t) = ?
      -- λ' a (ρ Var.↑ /Var ⊢substCtx (ktx/Var-∷ a ρ Γ) ⊢t)
    s /Var (⊢t [ b ])          = (s /Var ⊢t) [ b ]
    s /Var (⊢s · ⊢t)           = (s /Var ⊢s) · (s /Var ⊢t)
    s /Var (x)           = ?
  
    -- Weakening of terms with additional term variables lifted to
    -- well-typed terms.
    weaken : ∀ {ν n} {K : Ktx ν n} {t : Term ν n} {a b : Type ν} →
             K ⊢ t ∈ a → b ∷Γ K ⊢ TmTm.weaken t ∈ a
    weaken {K = K} {b = b} ⊢t = ? -- Var.wk /Var ⊢substCtx (C.wkVar-/Var-∷ Γ b) ⊢t
  
    -- Weakening of terms with additional term variables lifted to
    -- collections of well-typed terms.
    weakenAll : ∀ {ν n k} {K : Ktx ν n} {ts : Vec (Term ν n) k}
                  {as : Vec (Type ν) k} {b : Type ν} →
                K ⊢ⁿ ts ∈ as → (b ∷Γ K) ⊢ⁿ map TmTm.weaken ts ∈ as
    weakenAll {ts = []}    {[]}    []         = []
    weakenAll {ts = _ ∷ _} {_ ∷ _} (⊢t ∷ ⊢ts) = weaken ⊢t ∷ weakenAll ⊢ts
  
    -- Lifting of well-typed term substitutions.
    _↑ : ∀ {ν n} {Γ : Ktx ν n} {Δ : Ktx ν n} {ρ b} →
         Γ ⇒ Δ ⊢ ρ → b ∷Γ Γ ⇒ b ∷Γ Δ ⊢ ρ TmTm.↑
    ⊢ρ ↑ = var zero ∷ weakenAll ⊢ρ
  
    -- The well-typed identity substitution.
    id : ∀ {ν n} {K : Ktx ν n} → K ⇒ K ⊢ TmTm.id
    id {K = K} = ?
    -- id {zero}  {._} {K = [] , _}    = []
    -- id {suc _} {._} {K = a ∷ Γ , _} = id ↑
  
    -- Well-typed weakening (as a substitution).
    wk : ∀ {m n} {Γ : Ktx n m} {a} → Γ ⇒ a ∷Γ Γ ⊢ TmTm.wk
    wk = weakenAll id
  
    -- A well-typed substitution which only replaces the first variable.
    sub : ∀ {ν n} {K : Ktx ν n} {t a} → K ⊢ t ∈ a → a ∷Γ K ⇒ K ⊢ TmTm.sub t
    sub ⊢t = ⊢t ∷ id
  
    -- Application of term substitutions lifted to well-typed terms
    _/_ : ∀ {ν n} {K : Ktx ν n} {Δ : Ktx ν n} {t a s} →
          K ⊢ t ∈ a → K ⇒ Δ ⊢ s → Δ ⊢ t TmTm./ s ∈ a
    new c       / ⊢ρ = new c
    var x       / ⊢ρ = lookup-⊢ x ⊢ρ
    _/_ {K = K} {Δ = Δ} {s = s} (Λ ⊢t) ⊢ρ = Λ (⊢t / weaken-⊢p)
      where
        weaken-⊢p : ktx-weaken K ⇒ ktx-weaken Δ ⊢ map tm-weaken s
        weaken-⊢p = (WtTypeLemmas.weakenAll ⊢ρ)
    λ' a ⊢t     / ⊢ρ = λ' a (⊢t / ⊢ρ ↑)
    (⊢t [ a ])  / ⊢ρ = (⊢t / ⊢ρ) [ a ]
    (⊢s · ⊢t)   / ⊢ρ = (⊢s / ⊢ρ) · (⊢t / ⊢ρ)
  
    -- Shorthand for well-typed single-variable term substitutions.
    _[/_] : ∀ {m n} {Γ : Ctx n m} {s t a b} →
            b ∷ Γ ⊢ s ∈ a → Γ ⊢ t ∈ b → Γ ⊢ s TmTm./ TmTm.sub t ∈ a
    ⊢s [/ ⊢t ] = ⊢s / sub ⊢t
  
    tm[/tm]-preserves : ∀ {ν n} {Γ : Ctx ν n} {t u a b} → 
                        b ∷ Γ ⊢ t ∈ a → Γ ⊢ u ∈ b → Γ ⊢ (t tm[/tm u ]) ∈ a
    tm[/tm]-preserves ⊢s ⊢t = ⊢s / sub ⊢t
  
  open WtTypeLemmas public using ()
    renaming (weaken to ⊢tp-weaken)
  open WtTermLemmas public using ()
    renaming (_/_ to _⊢/tp_; _[/_] to _⊢[/_]; weaken to ⊢weaken)
  -}
  
