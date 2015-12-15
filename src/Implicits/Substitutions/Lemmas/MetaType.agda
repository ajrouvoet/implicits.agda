open import Prelude renaming (lift to finlift) hiding (id; subst)

module Implicits.Substitutions.Lemmas.MetaType (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Implicits.Syntax.Type TC _tc≟_
open import Implicits.Syntax.Term TC _tc≟_ hiding (var)
open import Implicits.Syntax.Context TC _tc≟_
open import Implicits.WellTyped TC _tc≟_
open import Implicits.Substitutions TC _tc≟_
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas 
open import Data.Vec.Properties
open import Extensions.Substitution

module MetaTypeTypeLemmas where
  open MetaTypeTypeSubst hiding (_/✶_)
  open import Implicits.Syntax.MetaType TC _tc≟_
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

module MetaTypeMetaLemmas where
  open MetaTypeMetaSubst using (module Lifted; MetaLift)
  open import Implicits.Syntax.MetaType TC _tc≟_
  open import Data.Star as Star hiding (map)
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

    comm-↑-↑tp : ∀ {ν n n'} (s : Sub (flip T ν) n n') → (s ↑) ↑tp ≡ (s ↑tp) ↑
    comm-↑-↑tp s = begin
      (s ↑) ↑tp
        ≡⟨ refl ⟩
      map tpweaken (var zero ∷ map weaken s)
        ≡⟨ refl ⟩
      (tpweaken (var zero)) ∷ (map tpweaken (map weaken s))
        ≡⟨ cong₂ (λ x xs → x ∷ xs) (tpweaken-var zero) (sym $ map-∘ tpweaken weaken s) ⟩
      (var zero) ∷ (map (tpweaken ∘ weaken) s)
        ≡⟨ cong (λ u → var zero ∷ u) (sym $ map-cong comm-weaken-tpweaken s) ⟩
      (var zero) ∷ (map (weaken ∘ tpweaken) s)
        ≡⟨ cong (λ u → (var zero) ∷ u) (map-∘ weaken tpweaken s) ⟩
      (s ↑tp) ↑ ∎

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

    module _ where
      open MetaTypeTypeSubst using () renaming (weaken to mtt-weaken)

      postulate ↑tp-mtt-weaken : ∀ {ν m n} x (s : Sub (flip T ν) m n) →
                                 (mtt-weaken x) / (s ↑tp) ≡ mtt-weaken (x / s)

      tpweaken-subs-var : ∀ {ν n n'} x (ρs : Subs (flip T ν) n n') →
                          (simpl (mvar x)) /✶ (tpweaken-subs ρs)
                            ≡ mtt-weaken ((simpl (mvar x)) /✶ ρs) 
      tpweaken-subs-var x ε = refl
      tpweaken-subs-var x (s ◅ ρs) = begin
        (simpl (mvar x)) /✶ (Star.map _↑tp (s ◅ ρs))
          ≡⟨ refl ⟩
        (simpl (mvar x)) /✶ (tpweaken-subs ρs) / (s ↑tp)
          ≡⟨ cong (flip _/_ (_↑tp s)) (tpweaken-subs-var x ρs) ⟩
        (mtt-weaken ((simpl (mvar x)) /✶ ρs)) / (s ↑tp)
          ≡⟨ ↑tp-mtt-weaken (simpl (mvar x) /✶ ρs) s ⟩
        mtt-weaken ((simpl (mvar x)) /✶ (s ◅ ρs)) ∎

  module _ {T₁ T₂} {lift₁ : MetaLift T₁} {lift₂ : MetaLift T₂} where
    open MetaTypeTypeSubst using () renaming (weaken to mtt-weaken)

    open Lifted lift₁ using () renaming (_↑✶_ to _↑✶₁_; _/✶_ to _/✶₁_; _↑tp to _↑tp₁)
    open Lifted lift₂ using () renaming (_↑✶_ to _↑✶₂_; _/✶_ to _/✶₂_; _↑tp to _↑tp₂)

    open MetaTypeAppLemmas

    weaken-hyp : ∀ {ν n n'} (ρs₁ : Subs (flip T₁ ν) n n') (ρs₂ : Subs (flip T₂ ν) n n') →
                        (∀ k x → (simpl (mvar x)) /✶₁ ρs₁ ↑✶₁ k ≡ (simpl (mvar x)) /✶₂ ρs₂ ↑✶₂ k) →  
                        (∀ k x → (simpl (mvar x)) /✶₁ (tpweaken-subs lift₁ ρs₁) ↑✶₁ k ≡ (simpl (mvar x)) /✶₂ (tpweaken-subs lift₂ ρs₂) ↑✶₂ k)
    weaken-hyp ρs₁ ρs₂ hyp k x = begin
      simpl (mvar x) /✶₁ (tpweaken-subs lift₁ ρs₁) ↑✶₁ k
        ≡⟨ cong (λ u → simpl (mvar x) /✶₁ u) (comm-tpweaken-↑✶ lift₁ k ρs₁) ⟩
      simpl (mvar x) /✶₁ tpweaken-subs lift₁ (ρs₁ ↑✶₁ k)
        ≡⟨ tpweaken-subs-var lift₁ x (ρs₁ ↑✶₁ k) ⟩
      mtt-weaken (simpl (mvar x) /✶₁ (ρs₁ ↑✶₁ k))
        ≡⟨ cong mtt-weaken (hyp k x) ⟩
      mtt-weaken (simpl (mvar x) /✶₂ (ρs₂ ↑✶₂ k))
        ≡⟨ sym $ tpweaken-subs-var lift₂ x (ρs₂ ↑✶₂ k) ⟩
      simpl (mvar x) /✶₂ tpweaken-subs lift₂ (ρs₂ ↑✶₂ k)
        ≡⟨ cong (λ u → simpl (mvar x) /✶₂ u) (sym $ comm-tpweaken-↑✶ lift₂ k ρs₂) ⟩
      simpl (mvar x) /✶₂ (tpweaken-subs lift₂ ρs₂) ↑✶₂ k ∎

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
        ≡⟨ cong ∀' (/✶-↑✶ (tpweaken-subs lift₁ ρs₁) (tpweaken-subs lift₂ ρs₂) (weaken-hyp ρs₁ ρs₂ hyp) k t ) ⟩
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

  open MetaTypeMetaSubst using (open-meta; _↑tp)

  us↑-⊙-sub-u≡u∷us : ∀ {ν m} (u : MetaType zero ν) (us : Sub (flip MetaType ν) m zero) →
                     us ↑ ⊙ sub u ≡ u ∷ us
  us↑-⊙-sub-u≡u∷us {ν} {m} u us = cong (λ v → u ∷ v) map-weaken-⊙-sub

  open-mvar : ∀ {ν m} (x : Fin m) → open-meta {ν = ν} (simpl (mvar x)) ≡ simpl (mvar (suc x))
  open-mvar x = weaken-var

  open-tvar-suc : ∀ {ν m} (x : Fin m) → open-meta {ν} (simpl (tvar (suc x))) ≡ simpl (tvar x)
  open-tvar-suc x = MetaTypeTypeLemmas.suc-/-sub {t = (simpl (tvar x))}
