module Implicits.Calculus.Denotational where

open import Prelude

open import Implicits.Calculus.WellTyped
open import Implicits.SystemF.WellTyped as F using ()
open import Extensions.ListFirst
open import Data.Fin.Substitution
open import Data.Vec.Properties

⟦_⟧tp : ∀ {ν} → Type ν → F.Type ν
⟦ tvar n ⟧tp = F.tvar n
⟦ a →' b ⟧tp = ⟦ a ⟧tp F.→' ⟦ b ⟧tp
⟦ ∀' x ⟧tp = F.∀' ⟦ x ⟧tp
⟦ a ⇒ b ⟧tp = ⟦ a ⟧tp F.→' ⟦ b ⟧tp

⟦_⟧ctx : ∀ {ν n} → Ktx ν n → F.Ctx ν n
⟦ Γ , Δ ⟧ctx = map ⟦_⟧tp Γ

-- construct an System F term from an implicit resolution
⟦_⟧i : ∀ {ν n} {K : Ktx ν n} {a} → K Δ↝ a → F.Term ν n

⟦_⟧ : ∀ {ν n} {K : Ktx ν n} {t a} → K ⊢ t ∈ a → F.Term ν n
⟦_⟧ (var x) = F.var x
⟦_⟧ (Λ t) = F.Λ ⟦ t ⟧
⟦_⟧ (λ' a x) = F.λ' ⟦ a ⟧tp ⟦ x ⟧
⟦_⟧ (f [ b ]) = F._[_] ⟦ f ⟧ ⟦ b ⟧tp
⟦_⟧ (f · e) = ⟦ f ⟧ F.· ⟦ e ⟧
⟦_⟧ (ρ a x) = F.λ' ⟦ a ⟧tp ⟦ x ⟧
⟦_⟧ (_⟨⟩ f e∈Δ) = ⟦ f ⟧ F.· ⟦ e∈Δ ⟧i
⟦_⟧ (implicit_in'_ {a = a} t e) = (F.λ' ⟦ a ⟧tp ⟦ e ⟧) F.· ⟦ t ⟧

⟦_⟧i (r , p) with first⟶witness p
⟦_⟧i {ν} {n} {proj₁ , proj₂} (a₁ , p) | by-value x = {!!}
⟦_⟧i {ν} {n} {proj₁ , proj₂} (._ , p) | yields x x₁ = {!!}

-- lookup in and interpreted context Γ is equivalent to interpreting a type, looked up in K
lookup⋆⟦⟧ctx : ∀ {ν n} (K : Ktx ν n) x → lookup x ⟦ K ⟧ctx ≡ ⟦ lookup x $ proj₁ K ⟧tp
lookup⋆⟦⟧ctx K x = sym $ lookup⋆map (proj₁ K) ⟦_⟧tp x

module Lemmas where
  module TS = TypeSubst
  module FTS = F.TypeSubst
  
  private
    module tss = Simple TS.simple
    module ftss = Simple FTS.simple

  -- implicitly constructed F-terms preserve type
  postulate ⟦⟧i-wt-lemma : ∀ {ν n} {K : Ktx ν n} {a} (i : K Δ↝ a) → ⟦ K ⟧ctx F.⊢ ⟦ i ⟧i ∈ ⟦ a ⟧tp

  -- type in type substitution commutes with type interpretation
  postulate tp/tp⋆⟦⟧ctx : ∀ {ν} (a : Type (suc ν)) b → ⟦ a tp[/tp b ] ⟧tp ≡ ⟦ a ⟧tp F.tp[/tp ⟦ b ⟧tp ]

  postulate weaken⋆⟦_⟧tp : ∀ {ν} → _≗_ {A = Type ν} (⟦_⟧tp ∘ tss.weaken) (ftss.weaken ∘ ⟦_⟧tp)

  map-weaken⋆map-⟦⟧tp : ∀ {ν n} (xs : Vec (Type ν) n) → (map ⟦_⟧tp (map tss.weaken xs)) ≡ (map ftss.weaken (map ⟦_⟧tp xs))
  map-weaken⋆map-⟦⟧tp xs = begin
    (map ⟦_⟧tp ∘ map tss.weaken) xs
     ≡⟨ sym $ (map-∘ ⟦_⟧tp tss.weaken) xs ⟩
    map (⟦_⟧tp ∘ tss.weaken) xs
     ≡⟨ (map-cong weaken⋆⟦_⟧tp) xs ⟩
    map (ftss.weaken ∘ ⟦_⟧tp) xs
     ≡⟨ (map-∘ ftss.weaken ⟦_⟧tp) xs ⟩ 
    map ftss.weaken (map ⟦_⟧tp xs) ∎
     
  map-⟦⟧tp-id≡fid : ∀ {n} → map ⟦_⟧tp (TS.id {n}) ≡ FTS.id
  map-⟦⟧tp-id≡fid {zero} = refl
  map-⟦⟧tp-id≡fid {suc n} = begin
    map ⟦_⟧tp (tvar zero ∷ map tss.weaken (TS.id {n})) 
      ≡⟨ refl ⟩
    F.tvar zero ∷ (map ⟦_⟧tp (map tss.weaken (TS.id {n}))) 
      ≡⟨ cong (_∷_ (F.tvar zero)) (map-weaken⋆map-⟦⟧tp (TS.id {n})) ⟩
    F.tvar zero ∷ (map ftss.weaken (map ⟦_⟧tp (TS.id {n}))) 
      ≡⟨ cong (λ e → F.tvar zero ∷ (map ftss.weaken e)) map-⟦⟧tp-id≡fid ⟩
    F.tvar zero ∷ (map ftss.weaken (FTS.id {n})) 
      ≡⟨ refl ⟩
    FTS.id ∎
  
  map-⟦⟧tp-wk≡fwk : ∀ {n} → map ⟦_⟧tp (TS.wk {n}) ≡ FTS.wk {n}
  map-⟦⟧tp-wk≡fwk = begin
    map ⟦_⟧tp TS.wk ≡⟨ map-weaken⋆map-⟦⟧tp TS.id ⟩
    map ftss.weaken (map ⟦_⟧tp TS.id) ≡⟨ cong (map ftss.weaken) map-⟦⟧tp-id≡fid ⟩
    FTS.wk ∎

  map-⟦⟧tp⋆↑ :  ∀ {ν n} (v : Vec (Type ν) n) → map ⟦_⟧tp (v TS.↑) ≡ (map ⟦_⟧tp  v) FTS.↑
  map-⟦⟧tp⋆↑ xs = begin
    F.tvar zero ∷ (map ⟦_⟧tp (map tss.weaken xs)) 
      ≡⟨ cong (_∷_ (F.tvar zero)) (map-weaken⋆map-⟦⟧tp xs) ⟩
    F.tvar zero ∷ (map ftss.weaken (map ⟦_⟧tp xs)) 
      ≡⟨ refl ⟩
    (map ⟦_⟧tp xs) FTS.↑ ∎

  -- type substitution commutes with interpreting types
  /⋆⟦⟧tp : ∀ {ν μ} (tp : Type ν) (σ : Sub Type ν μ) → ⟦ tp TS./ σ ⟧tp ≡ ⟦ tp ⟧tp FTS./ (map ⟦_⟧tp σ)
  /⋆⟦⟧tp (tvar n) σ = begin
    ⟦ lookup n σ ⟧tp ≡⟨ lookup⋆map σ ⟦_⟧tp n ⟩
    ⟦ tvar n ⟧tp FTS./ (map ⟦_⟧tp σ) ∎
  /⋆⟦⟧tp {ν} (∀' tp) σ = begin
    F.∀' (⟦ tp TS./ (σ TS.↑) ⟧tp) ≡⟨ cong F.∀' (/⋆⟦⟧tp tp (σ TS.↑)) ⟩
    F.∀' (⟦ tp ⟧tp FTS./ (map ⟦_⟧tp (σ TS.↑)))  ≡⟨ cong (λ e → F.∀' (⟦ tp ⟧tp FTS./ e)) (map-⟦⟧tp⋆↑ σ) ⟩
    ⟦ ∀' tp ⟧tp FTS./ (map ⟦_⟧tp σ) ∎

  /⋆⟦⟧tp (l →' r) σ = cong₂ F._→'_ (/⋆⟦⟧tp l σ) (/⋆⟦⟧tp r σ)
  /⋆⟦⟧tp (l ⇒ r) σ = cong₂ F._→'_ (/⋆⟦⟧tp l σ) (/⋆⟦⟧tp r σ)

  -- type weakening commutes with interpreting types
  weaken-tp⋆⟦⟧tp : ∀ {ν} (tp : Type ν) → ⟦ tp TS./ TS.wk ⟧tp ≡ ⟦ tp ⟧tp FTS./ FTS.wk
  weaken-tp⋆⟦⟧tp tp = begin
    ⟦ tp TS./ TS.wk ⟧tp 
      ≡⟨ /⋆⟦⟧tp tp TS.wk ⟩
    ⟦ tp ⟧tp FTS./ (map ⟦_⟧tp TS.wk) 
      ≡⟨ cong (λ e → ⟦ tp ⟧tp FTS./ e) map-⟦⟧tp-wk≡fwk ⟩
    ⟦ tp ⟧tp FTS./ FTS.wk ∎

  -- context weakening commutes with interpreting contexts
  ctx-weaken⋆⟦⟧ctx : ∀ {ν n} (K : Ktx ν n) → ⟦ ktx-weaken K ⟧ctx ≡ F.ctx-weaken ⟦ K ⟧ctx
  ctx-weaken⋆⟦⟧ctx ([] , Δ) = refl
  ctx-weaken⋆⟦⟧ctx (x ∷ Γ , Δ) with ctx-weaken⋆⟦⟧ctx (Γ , Δ)
  ctx-weaken⋆⟦⟧ctx (x ∷ Γ , Δ) | ih = begin
    ⟦ ktx-weaken (x ∷ Γ , Δ) ⟧ctx ≡⟨ refl ⟩ 
    ⟦ x TS./ TS.wk ⟧tp ∷ xs ≡⟨ cong (flip _∷_ xs) (weaken-tp⋆⟦⟧tp x) ⟩ 
    ⟦ x ⟧tp FTS./ FTS.wk ∷ ⟦ ktx-weaken (Γ , Δ) ⟧ctx ≡⟨ cong (_∷_ (⟦ x ⟧tp FTS./ FTS.wk)) ih ⟩
    ⟦ x ⟧tp FTS./ FTS.wk ∷ F.ctx-weaken ⟦ Γ , Δ ⟧ctx ≡⟨ refl ⟩
    F.ctx-weaken ⟦ x ∷ Γ , Δ ⟧ctx ∎
    where
      xs = (map ⟦_⟧tp $ map (λ s → s TS./ TS.wk) Γ)

open Lemmas

-- interpretation of well-typed terms in System F preserves type
⟦⟧-preserves-tp : ∀ {ν n} {K : Ktx ν n} {t a} → (wt-t : K ⊢ t ∈ a) → ⟦ K ⟧ctx F.⊢ ⟦ wt-t ⟧ ∈ ⟦ a ⟧tp
⟦⟧-preserves-tp {K = K} (var x) = subst-wt-var (lookup⋆⟦⟧ctx K x) (F.var x)
  where
    subst-wt-var = subst (λ a → ⟦ K ⟧ctx F.⊢ (F.var x) ∈ a)
⟦⟧-preserves-tp {K = K} {a = ∀' a} (Λ wt-e) with ⟦⟧-preserves-tp wt-e 
... | f-wt-e = F.Λ (subst-wt-ctx (ctx-weaken⋆⟦⟧ctx K) f-wt-e)
  where
    subst-wt-ctx = subst (λ c → c F.⊢ ⟦ wt-e ⟧ ∈ ⟦ a ⟧tp)
⟦⟧-preserves-tp (λ' a wt-e) with ⟦⟧-preserves-tp wt-e
⟦⟧-preserves-tp (λ' a wt-e) | x = F.λ' ⟦ a ⟧tp x
⟦⟧-preserves-tp {K = K} (_[_] {a = a} wt-tc b) with ⟦⟧-preserves-tp wt-tc
... | x = subst-tp (sym $ tp/tp⋆⟦⟧ctx a b) (x F.[ ⟦ b ⟧tp ])
  where
    subst-tp = subst (λ c → ⟦ K ⟧ctx F.⊢ ⟦ wt-tc [ b ] ⟧ ∈ c) 
⟦⟧-preserves-tp (wt-f · wt-e) with ⟦⟧-preserves-tp wt-f | ⟦⟧-preserves-tp wt-e
⟦⟧-preserves-tp (wt-f · wt-e) | x | y = x F.· y
⟦⟧-preserves-tp (ρ a wt-e) with ⟦⟧-preserves-tp wt-e
⟦⟧-preserves-tp (ρ a wt-e) | x = F.λ' ⟦ a ⟧tp x
⟦⟧-preserves-tp (_⟨⟩ wt-r e) with ⟦⟧-preserves-tp wt-r 
⟦⟧-preserves-tp (_⟨⟩ wt-r e) | f-wt-r = let wt-f-e = ⟦⟧i-wt-lemma e in f-wt-r F.· wt-f-e
⟦⟧-preserves-tp (implicit wt-e₁ in' wt-e₂) with ⟦⟧-preserves-tp wt-e₁ | ⟦⟧-preserves-tp wt-e₂
⟦⟧-preserves-tp (implicit_in'_ {a = a} wt-e₁ wt-e₂) | x | y = (F.λ' ⟦ a ⟧tp y) F.· x
