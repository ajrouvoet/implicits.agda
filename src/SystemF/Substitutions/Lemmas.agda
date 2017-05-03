module SystemF.Substitutions.Lemmas where

open import Prelude hiding (module Fin; id)

open import SystemF.WellTyped
open import SystemF.Substitutions

open import Data.Fin as Fin using ()
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Vec hiding ([_])

open import Extensions.Substitution
open import Extensions.Vec
open import Data.Vec.Properties

import Category.Applicative.Indexed as Applicative
open Applicative.Morphism using (op-<$>)

module TypeLemmas where
  open TypeSubst using (module Lifted; module TypeApp)
  open import Data.Fin.Substitution.Lemmas
  open import Data.Fin.Substitution.Lemmas public using (module VarLemmas)
  open import Data.Star using (Star; ε; _◅_)

  typeLemmas : TermLemmas Type
  typeLemmas = record { termSubst = TypeSubst.typeSubst; app-var = refl ; /✶-↑✶ = Lemma./✶-↑✶ }
    where
      module Lemma {T₁ T₂} {lift₁ : Lift T₁ Type} {lift₂ : Lift T₂ Type} where

        open Lifted lift₁ using () renaming (_↑✶_ to _↑✶₁_; _/✶_ to _/✶₁_)
        open Lifted lift₂ using () renaming (_↑✶_ to _↑✶₂_; _/✶_ to _/✶₂_)

        /✶-↑✶ : ∀ {m n} (σs₁ : Subs T₁ m n) (σs₂ : Subs T₂ m n) →
                          (∀ k x → tvar x /✶₁ σs₁ ↑✶₁ k ≡ tvar x /✶₂ σs₂ ↑✶₂ k) →
                          ∀ k t → t /✶₁ σs₁ ↑✶₁ k ≡ t /✶₂ σs₂ ↑✶₂ k
        /✶-↑✶ ρs₁ ρs₂ hyp k (tvar x) = hyp k x
        /✶-↑✶ ρs₁ ρs₂ hyp k (tc c) = begin
            (tc c) /✶₁ ρs₁ ↑✶₁ k
          ≡⟨ TypeApp.tc-/✶-↑✶ _ k ρs₁ ⟩
            (tc c)
          ≡⟨ sym $ TypeApp.tc-/✶-↑✶ _ k ρs₂ ⟩
            (tc c) /✶₂ ρs₂ ↑✶₂ k ∎
        /✶-↑✶ ρs₁ ρs₂ hyp k (a ⟶ b) = begin
            (a ⟶  b) /✶₁ ρs₁ ↑✶₁ k
          ≡⟨ TypeApp.⟶-/✶-↑✶ _ k ρs₁ ⟩
            (a /✶₁ ρs₁ ↑✶₁ k) ⟶ (b /✶₁ ρs₁ ↑✶₁ k)
          ≡⟨ cong₂ _⟶_ (/✶-↑✶ ρs₁ ρs₂ hyp k a) (/✶-↑✶ ρs₁ ρs₂ hyp k b) ⟩
            (a /✶₂ ρs₂ ↑✶₂ k) ⟶ (b /✶₂ ρs₂ ↑✶₂ k)
          ≡⟨ sym (TypeApp.⟶-/✶-↑✶ _ k ρs₂) ⟩
            (a ⟶ b) /✶₂ ρs₂ ↑✶₂ k
          ∎
        /✶-↑✶ ρs₁ ρs₂ hyp k (a →' b) = begin
            (a →' b) /✶₁ ρs₁ ↑✶₁ k
          ≡⟨ TypeApp.→'-/✶-↑✶ _ k ρs₁ ⟩
            (a /✶₁ ρs₁ ↑✶₁ k) →' (b /✶₁ ρs₁ ↑✶₁ k)
          ≡⟨ cong₂ _→'_ (/✶-↑✶ ρs₁ ρs₂ hyp k a) (/✶-↑✶ ρs₁ ρs₂ hyp k b) ⟩
            (a /✶₂ ρs₂ ↑✶₂ k) →' (b /✶₂ ρs₂ ↑✶₂ k)
          ≡⟨ sym (TypeApp.→'-/✶-↑✶ _ k ρs₂) ⟩
            (a →' b) /✶₂ ρs₂ ↑✶₂ k
          ∎
        /✶-↑✶ ρs₁ ρs₂ hyp k (∀' a) = begin
          (∀' a) /✶₁ ρs₁ ↑✶₁ k        ≡⟨ TypeApp.∀'-/✶-↑✶ _ k ρs₁ ⟩
          ∀' (a /✶₁ ρs₁ ↑✶₁ (1 + k))  ≡⟨ cong ∀' (/✶-↑✶ ρs₁ ρs₂ hyp (1 + k) a) ⟩
          ∀' (a /✶₂ ρs₂ ↑✶₂ (1 + k))  ≡⟨ sym (TypeApp.∀'-/✶-↑✶ _ k ρs₂) ⟩
          (∀' a) /✶₂ ρs₂ ↑✶₂ k        ∎

  module tpl = TermLemmas typeLemmas

  -- The above lemma /✶-↑✶ specialized to single substitutions
  /-↑⋆ : ∀ {T₁ T₂} {lift₁ : Lift T₁ Type} {lift₂ : Lift T₂ Type} →
         let open Lifted lift₁ using () renaming (_↑⋆_ to _↑⋆₁_; _/_ to _/₁_)
             open Lifted lift₂ using () renaming (_↑⋆_ to _↑⋆₂_; _/_ to _/₂_)
         in
         ∀ {n k} (ρ₁ : Sub T₁ n k) (ρ₂ : Sub T₂ n k) →
         (∀ i x → tvar x /₁ ρ₁ ↑⋆₁ i ≡ tvar x /₂ ρ₂ ↑⋆₂ i) →
          ∀ i a → a /₁ ρ₁ ↑⋆₁ i ≡ a /₂ ρ₂ ↑⋆₂ i
  /-↑⋆ ρ₁ ρ₂ hyp i a = tpl./✶-↑✶ (ρ₁ ◅ ε) (ρ₂ ◅ ε) hyp i a

  open AdditionalLemmas typeLemmas public
  open tpl public

  /Var-/ : ∀ {ν μ} (t : Type ν) (s : Sub Fin ν μ) → t /Var s ≡ t / (map tvar s)
  /Var-/ (tc c) s = refl
  /Var-/ (tvar n) s = lookup⋆map s tvar n
  /Var-/ (a →' b) s = cong₂ _→'_ (/Var-/ a s) (/Var-/ b s)
  /Var-/ (a ⟶ b) s = cong₂ _⟶_ (/Var-/ a s) (/Var-/ b s)
  /Var-/ (∀' t) s = begin
    ∀' (t /Var (s Var.↑))
      ≡⟨ cong ∀' $ /Var-/ t (s Var.↑) ⟩
    ∀' (t / (map tvar $ s Var.↑))
      ≡⟨ cong (λ u → ∀' (t / u)) (map-var-↑ refl) ⟩
    ∀' t / (map tvar s) ∎

  a-/Var-varwk↑-/-sub0≡a : ∀ {n} (a : Type (suc n)) → (a /Var Var.wk Var.↑) / sub (tvar zero) ≡ a
  a-/Var-varwk↑-/-sub0≡a a = begin
    (a /Var Var.wk Var.↑) / (sub $ tvar zero)
      ≡⟨ cong (λ u → u / (sub $ tvar zero)) (/Var-/ a $ Var.wk Var.↑) ⟩
    (a / (map tvar $ Var.wk Var.↑)) / sub (tvar zero)
      ≡⟨ cong (λ u → (a / u) / (sub $ tvar zero)) (map-var-↑ map-var-varwk≡wk) ⟩
    (a / wk ↑) / (sub $ tvar zero)
      ≡⟨ a/wk↑/sub0≡a a ⟩
    a ∎

-- Lemmas about type substitutions in terms.
module TermTypeLemmas where
  open TermTypeSubst public

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
     ∀ i {m} (t : Term (i + n) m)  → t /₁ ρ₁ ↑⋆₁ i ≡ t /₂ ρ₂ ↑⋆₂ i
  /-↑⋆ ρ₁ ρ₂ hyp i (var x)      = refl
  /-↑⋆ ρ₁ ρ₂ hyp i (Λ t)        = cong Λ      (/-↑⋆ ρ₁ ρ₂ hyp (1 + i) t)
  /-↑⋆ ρ₁ ρ₂ hyp i (λ' a t)     =
    cong₂ λ'     (T./-↑⋆ ρ₁ ρ₂ hyp i a)       (/-↑⋆ ρ₁ ρ₂ hyp i t)
  /-↑⋆ ρ₁ ρ₂ hyp i (t [ b ])    =
    cong₂ _[_]     (/-↑⋆ ρ₁ ρ₂ hyp i t)     (T./-↑⋆ ρ₁ ρ₂ hyp i b)
  /-↑⋆ ρ₁ ρ₂ hyp i (s · t)      =
    cong₂ _·_      (/-↑⋆ ρ₁ ρ₂ hyp i s)       (/-↑⋆ ρ₁ ρ₂ hyp i t)

  /-wk : ∀ {m n} (t : Term m n) → t / TypeSubst.wk ≡ weaken t
  /-wk t = /-↑⋆ TypeSubst.wk VarSubst.wk (λ k x → begin
    tvar x T./ T.wk T.↑⋆ k ≡⟨ T.var-/-wk-↑⋆ k x ⟩
    tvar (Fin.lift k suc x) ≡⟨ cong tvar (sym (V.var-/-wk-↑⋆ k x)) ⟩
    tvar (lookup x (V.wk V.↑⋆ k)) ≡⟨ refl ⟩
    tvar x TS./Var V.wk V.↑⋆ k ∎) 0 t

module CtxLemmas where
  open CtxSubst public

  private module Tp  = TypeLemmas
  private module Var = VarSubst

  -- Term variable substitution (renaming) commutes with type
  -- substitution.
  /Var-/ : ∀ {m ν n l} (ρ : Sub Fin m n) (Γ : Ctx ν n) (σ : Sub Type ν l) →
           (ρ /Var Γ) / σ ≡ ρ /Var (Γ / σ)
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
    (ρ /Var Γ) / Tp.wk   ≡⟨ /Var-/ ρ Γ Tp.wk ⟩
    ρ /Var (weaken Γ)    ∎

  -- Term variable substitution (renaming) commutes with term variable
  -- lookup in typing context.
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

  ctx-weaken-sub-vanishes : ∀ {ν n} {Γ : Ctx ν n} {a} → (ctx-weaken Γ) ctx/ (Tp.sub a) ≡ Γ
  ctx-weaken-sub-vanishes {Γ = Γ} {a} = begin
    (Γ ctx/ Tp.wk) ctx/ (Tp.sub a)
      ≡⟨ sym $ map-∘ (λ s → s tp/tp Tp.sub a) (λ s → s tp/tp Tp.wk) Γ ⟩
    (map (λ s → s tp/tp Tp.wk tp/tp (Tp.sub a)) Γ)
      ≡⟨ map-cong (TypeLemmas.wk-sub-vanishes) Γ ⟩
    (map (λ s → s) Γ) ≡⟨ map-id Γ ⟩
    Γ ∎

private
  ⊢subst : ∀ {m n} {Γ₁ Γ₂ : Ctx n m} {t₁ t₂ : Term n m} {a₁ a₂ : Type n} →
    Γ₁ ≡ Γ₂ → t₁ ≡ t₂ → a₁ ≡ a₂ → Γ₁ ⊢ t₁ ∈ a₁ → Γ₂ ⊢ t₂ ∈ a₂
  ⊢subst refl refl refl hyp = hyp

  ⊢substCtx : ∀ {m n} {Γ₁ Γ₂ : Ctx n m} {t : Term n m} {a : Type n} →
    Γ₁ ≡ Γ₂ → Γ₁ ⊢ t ∈ a → Γ₂ ⊢ t ∈ a
  ⊢substCtx refl hyp = hyp

  ⊢substTp : ∀ {m n} {Γ : Ctx n m} {t : Term n m} {a₁ a₂ : Type n} →
    a₁ ≡ a₂ → Γ ⊢ t ∈ a₁ → Γ ⊢ t ∈ a₂
  ⊢substTp refl hyp = hyp

module WtTypeLemmas where
  open TypeLemmas hiding (_/_; var; weaken)
  private
    module Tp = TypeLemmas
    module TmTp = TermTypeLemmas
    module C  = CtxLemmas

  infixl 8 _/_

  -- Type substitutions lifted to well-typed terms
  _/_ : ∀ {m n k} {Γ : Ctx n m} {t : Term n m} {a : Type n} →
        Γ ⊢ t ∈ a → (σ : Sub Type n k) → Γ C./ σ ⊢ t TmTp./ σ ∈ a Tp./ σ
  var x             / σ = ⊢substTp (lookup-⊙ x) (var x)
  _/_ {Γ = Γ} (Λ ⊢t)  σ = Λ (⊢substCtx eq (⊢t / σ ↑))
    where
      eq : (ctx-weaken Γ) C./ (σ Tp.↑) ≡ ctx-weaken (Γ C./ σ)
      eq = begin
        (map (λ s → s tp/tp Tp.wk) Γ) C./ (σ Tp.↑)
          ≡⟨ cong (λ a → a C./ (σ Tp.↑)) (map-cong (λ a → Tp./-wk {t = a}) Γ) ⟩
        (map Tp.weaken Γ) ⊙ (σ Tp.↑)
          ≡⟨ sym $ map-weaken-⊙ Γ σ ⟩
        map Tp.weaken (Γ ⊙ σ)
          ≡⟨ (map-cong (λ a → sym $ Tp./-wk {t = a}) (Γ ⊙ σ)) ⟩
        ctx-weaken (Γ C./ σ) ∎
  λ' a ⊢t           / σ = λ' (a Tp./ σ) (⊢t / σ)
  _[_] {a = a} ⊢t b / σ = ⊢substTp (sym (sub-commutes a)) ((⊢t / σ) [ b Tp./ σ ])
  ⊢s · ⊢t           / σ = (⊢s / σ) · (⊢t / σ)

  -- Weakening of terms with additional type variables lifted to
  -- well-typed terms.
  weaken : ∀ {m n} {Γ : Ctx n m} {t : Term n m} {a : Type n} →
           Γ ⊢ t ∈ a → ctx-weaken Γ ⊢ TmTp.weaken t ∈ Tp.weaken a
  weaken {t = t} {a = a} ⊢t = ⊢subst refl (TmTp./-wk t) (/-wk {t = a}) (⊢t / wk)

  -- Weakening of terms with additional type variables lifted to
  -- collections of well-typed terms.
  weakenAll : ∀ {m n k} {Γ : Ctx n m} {ts : Vec (Term n m) k}
                {as : Vec (Type n) k} → Γ ⊢ⁿ ts ∈ as →
                ctx-weaken Γ ⊢ⁿ map TmTp.weaken ts ∈ map Tp.weaken as
  weakenAll {ts = []}    {[]}    []         = []
  weakenAll {ts = _ ∷ _} {_ ∷ _} (⊢t ∷ ⊢ts) = weaken ⊢t ∷ weakenAll ⊢ts

  -- Shorthand for single-variable type substitutions in well-typed
  -- terms.
  _[/_] : ∀ {m n} {Γ : Ctx (1 + n) m} {t a} →
          Γ ⊢ t ∈ a → (b : Type n) → Γ C./ sub b ⊢ t TmTp./ sub b ∈ a Tp./ sub b
  ⊢t [/ b ] = ⊢t / sub b

  tm[/tp]-preserves : ∀ {ν n} {Γ : Ctx ν n} {t τ} → Γ ⊢ Λ t ∈ ∀' τ → ∀ a → Γ ⊢ (t tm[/tp a ]) ∈ τ tp[/tp a ]
  tm[/tp]-preserves {Γ = Γ} {t} {τ} (Λ p) a = ctx-subst C.ctx-weaken-sub-vanishes (p / (Tp.sub a))
    where
      ctx-subst = Prelude.subst (λ c → c ⊢ t tm[/tp a ] ∈ τ tp[/tp a ])

module WtTermLemmas where
  private
    module Tp  = TypeLemmas
    module TmTp  = TermTypeLemmas
    module TmTm  = TermTermSubst
    module Var = VarSubst
    module C   = CtxLemmas
    TmSub = TmTm.TermSub Term

  infix 4 _⇒_⊢_

  -- Well-typed term substitutions are collections of well-typed terms.
  _⇒_⊢_ : ∀ {ν m k} → Ctx ν m → Ctx ν k → TmSub ν m k → Set
  Γ ⇒ Δ ⊢ ρ = Δ ⊢ⁿ ρ ∈ Γ

  infixl 8  _/_ _/Var_
  infix  10 _↑

  -- Application of term variable substitutions (renaming) lifted to
  -- well-typed terms.
  _/Var_ : ∀ {m n k} {Γ : Ctx n k} {t : Term n m} {a : Type n}
             (ρ : Sub Fin m k) → ρ C./Var Γ ⊢ t ∈ a → Γ ⊢ t TmTm./Var ρ ∈ a
  _/Var_ {Γ = Γ} ρ (var x)   =
    ⊢substTp (sym (C./Var-lookup x ρ Γ)) (var (lookup x ρ))
  _/Var_ {Γ = Γ} ρ (Λ ⊢t)    =
    Λ    (ρ      /Var ⊢substCtx (C./Var-weaken ρ Γ) ⊢t)
  _/Var_ {Γ = Γ} ρ (λ' a ⊢t) =
    λ' a (ρ Var.↑ /Var ⊢substCtx (C./Var-∷ a ρ Γ) ⊢t)
  ρ /Var (⊢t [ b ])          = (ρ /Var ⊢t) [ b ]
  ρ /Var (⊢s · ⊢t)           = (ρ /Var ⊢s) · (ρ /Var ⊢t)

  -- Weakening of terms with additional term variables lifted to
  -- well-typed terms.
  weaken : ∀ {m n} {Γ : Ctx n m} {t : Term n m} {a b : Type n} →
           Γ ⊢ t ∈ a → b ∷ Γ ⊢ TmTm.weaken t ∈ a
  weaken {Γ = Γ} {b = b} ⊢t =
    Var.wk /Var ⊢substCtx (C.wkVar-/Var-∷ Γ b) ⊢t

  -- Weakening of terms with additional term variables lifted to
  -- collections of well-typed terms.
  weakenAll : ∀ {m n k} {Γ : Ctx n m} {ts : Vec (Term n m) k}
                {as : Vec (Type n) k} {b : Type n} →
              Γ ⊢ⁿ ts ∈ as → (b ∷ Γ) ⊢ⁿ map TmTm.weaken ts ∈ as
  weakenAll {ts = []}    {[]}    []         = []
  weakenAll {ts = _ ∷ _} {_ ∷ _} (⊢t ∷ ⊢ts) = weaken ⊢t ∷ weakenAll ⊢ts

  -- Lifting of well-typed term substitutions.
  _↑ : ∀ {m n k} {Γ : Ctx n m} {Δ : Ctx n k} {ρ b} →
       Γ ⇒ Δ ⊢ ρ → b ∷ Γ ⇒ b ∷ Δ ⊢ ρ TmTm.↑
  ⊢ρ ↑ = var zero ∷ weakenAll ⊢ρ

  -- The well-typed identity substitution.
  id : ∀ {m n} {Γ : Ctx n m} → Γ ⇒ Γ ⊢ TmTm.id
  id {zero}  {Γ = []}    = []
  id {suc m} {Γ = a ∷ Γ} = id ↑

  -- Well-typed weakening (as a substitution).
  wk : ∀ {m n} {Γ : Ctx n m} {a} → Γ ⇒ a ∷ Γ ⊢ TmTm.wk
  wk = weakenAll id

  -- A well-typed substitution which only replaces the first variable.
  sub : ∀ {m n} {Γ : Ctx n m} {t a} → Γ ⊢ t ∈ a → a ∷ Γ ⇒ Γ ⊢ TmTm.sub t
  sub ⊢t = ⊢t ∷ id

  -- Application of term substitutions lifted to well-typed terms
  _/_ : ∀ {m n k} {Γ : Ctx n m} {Δ : Ctx n k} {t a ρ} →
        Γ ⊢ t ∈ a → Γ ⇒ Δ ⊢ ρ → Δ ⊢ t TmTm./ ρ ∈ a
  var x       / ⊢ρ = lookup-⊢ x ⊢ρ
  _/_ {Γ = Γ} {Δ = Δ} {ρ = ρ} (Λ ⊢t) ⊢ρ = Λ (⊢t / weaken-⊢p)
    where
      weaken-⊢p : ctx-weaken Γ ⇒ ctx-weaken Δ ⊢ map TmTp.weaken ρ
      weaken-⊢p = (Prelude.subst
        (λ G → G ⇒ ctx-weaken Δ ⊢ map TmTp.weaken ρ) Tp.map-weaken (WtTypeLemmas.weakenAll ⊢ρ))
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
