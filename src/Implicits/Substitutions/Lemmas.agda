open import Prelude

module Implicits.Substitutions.Lemmas where

open import Implicits.Syntax.Type
open import Implicits.Syntax.Term hiding (var)
open import Implicits.Syntax.Context
open import Implicits.WellTyped
open import Implicits.Substitutions
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas 
open import Data.Vec.Properties
open import Extensions.Substitution
import Category.Applicative.Indexed as Applicative
open Applicative.Morphism using (op-<$>)

module TypeLemmas where
  open import Implicits.Substitutions.Lemmas.Type public

open import Implicits.Substitutions.Lemmas.MetaType public

{-
module SubstLemmas (_⊢ᵣ_ : ∀ {ν} → ICtx ν → Type ν → Set) where

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
    weaken : ∀ {ν n} {K : Ktx ν n} {t : Term ν n} {a b : Type ν} →
                       K ⊢ t ∈ a → b ∷Γ K ⊢ tmtm-weaken t ∈ a
    -- weaken {Γ = Γ} {b = b} ⊢t = Var.wk /Var ⊢substCtx (C.wkVar-/Var-∷ Γ b) ⊢t
  
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
        eq : (ktx-weaken Γ) ktx/ (σ Tp.↑) ≡ ktx-weaken (Γ ktx/ σ)
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
