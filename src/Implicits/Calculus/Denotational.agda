{-# OPTIONS --no-termination-check #-}
module Implicits.Calculus.Denotational where

open import Prelude

open import Implicits.Calculus.WellTyped
open import Implicits.Calculus.Substitutions
open import Implicits.SystemF as F using ()
open import Extensions.ListFirst
open import Data.Fin.Substitution
open import Data.Vec.Properties

module RewriteContext where

  -- rewrite context (relation between implicit and explicit context)
  _#_ : ∀ {ν n} (Γ : Ctx ν n) (Δ : ICtx ν) → Set
  Γ # Δ = All (λ i → i ∈ Γ) Δ

  K# : ∀ {ν n} (K : Ktx ν n) → Set
  K# (Γ , Δ) = Γ # Δ
  
  #tvar : ∀ {ν n} {K : Ktx ν n} → K# K → K# (ktx-weaken K)
  #tvar All.[] = All.[]
  #tvar (px All.∷ K#K) = (∈⋆map px (λ t → t pt/tp TypeSubst.wk)) All.∷ (#tvar K#K)

  #var : ∀ {ν n} {K : Ktx ν n} → (a : PolyType ν) → K# K → K# (a ∷Γ K)
  #var a All.[] = All.[]
  #var a (px All.∷ K#K) = there px All.∷ (#var a K#K)

  #ivar : ∀ {ν n} {K : Ktx ν n} → (a : PolyType ν) → K# K → K# (a ∷K K)
  #ivar a K#K = here All.∷ (All.map there K#K)

private
  module TS = TypeSubst
  open PTypeSubst using (_/_; _/tp_; _[/_]; weaken)
  open RewriteContext
  
  module TSS = Simple TS.simple
  module FTSS = Simple F.simple

⟦_⟧tp : ∀ {ν} → Type ν → F.Type ν
⟦ tvar n ⟧tp = F.tvar n
⟦ a →' b ⟧tp = ⟦ a ⟧tp F.→' ⟦ b ⟧tp
⟦ a ⇒ b ⟧tp = ⟦ a ⟧tp F.→' ⟦ b ⟧tp

⟦_⟧pt : ∀ {ν} → PolyType ν → F.Type ν
⟦ mono tp ⟧pt = ⟦ tp ⟧tp
⟦ ∀' x ⟧pt = F.∀' ⟦ x ⟧pt

⟦_⟧tps : ∀ {ν n} → Vec (Type ν) n → Vec (F.Type ν) n
⟦ v ⟧tps = map (⟦_⟧tp) v

⟦_⟧ctx : ∀ {ν n} → Ktx ν n → F.Ctx ν n
⟦ Γ , Δ ⟧ctx = map ⟦_⟧pt Γ

-- given a proof that some calculus type b is a specialization of a,
-- and an F-instance of a, we can build an F-instance of b
-- (it might seem more natural to first build a Calculus term and keep the interpretation out of this,
--    but that gives termination checking problems, since we could put more implicit applications in the 
--    constructed term)
inst : ∀ {ν n} {a b t} {K : F.Ctx ν n} → a ⊑ b → K F.⊢ t ∈ ⟦ a ⟧pt → ∃ λ t' → K F.⊢ t' ∈ ⟦ b ⟧pt

-- construct an System F term from an implicit resolution
⟦_,_⟧i : ∀ {ν n} {K : Ktx ν n} {a} → K Δ↝ a → K# K → ∃ λ t → ⟦ K ⟧ctx F.⊢ t ∈ ⟦ a ⟧pt

-- denotational semantics of well-typed terms
⟦_,_⟧ : ∀ {ν n} {K : Ktx ν n} {t} {a : PolyType ν} → K ⊢ t ∈ a → K# K → F.Term ν n
⟦_,_⟧ (var x) m = F.var x
⟦_,_⟧ (Λ t) m = F.Λ ⟦ t , #tvar m ⟧
⟦_,_⟧ (λ' a x) m = F.λ' ⟦ a ⟧tp ⟦ x , #var (mono a) m ⟧
⟦_,_⟧ (f [ b ]) m = F._[_] ⟦ f , m ⟧ ⟦ b ⟧tp
⟦_,_⟧ (f · e) m = ⟦ f , m ⟧ F.· ⟦ e , m ⟧
⟦_,_⟧ (ρ a x) m = F.λ' ⟦ a ⟧tp ⟦ x , #ivar (mono a) m ⟧
⟦_,_⟧ (_⟨⟩ f e∈Δ) m = ⟦ f , m ⟧ F.· (proj₁ ⟦ e∈Δ , m ⟧i)
⟦_,_⟧ (let'_in'_ {a = a} t e) m = (F.λ' ⟦ a ⟧pt ⟦ e , #var a m ⟧) F.· ⟦ t , m ⟧
⟦_,_⟧ (implicit_in'_ {a = a} t e) m = (F.λ' ⟦ a ⟧pt ⟦ e , #ivar a m ⟧) F.· ⟦ t , m ⟧

module Lemmas where

  -- lookup in and interpreted context Γ is equivalent to interpreting a type, looked up in K
  lookup⋆⟦⟧ctx : ∀ {ν n} (K : Ktx ν n) x → lookup x ⟦ K ⟧ctx ≡ ⟦ lookup x $ proj₁ K ⟧pt
  lookup⋆⟦⟧ctx K x = sym $ lookup⋆map (proj₁ K) ⟦_⟧pt x

  weaken⋆⟦_⟧tp : ∀ {ν} → _≗_ {A = Type ν} (⟦_⟧tp ∘ TSS.weaken) (FTSS.weaken ∘ ⟦_⟧tp)
  weaken⋆⟦ tvar n ⟧tp = refl
  weaken⋆⟦ a →' b ⟧tp = cong₂ F._→'_ weaken⋆⟦ a ⟧tp weaken⋆⟦ b ⟧tp 
  weaken⋆⟦ a ⇒ b ⟧tp = cong₂ F._→'_ weaken⋆⟦ a ⟧tp weaken⋆⟦ b ⟧tp 

  -- helper lemma on mapping type-semantics over weakend substitutions
  ⟦⟧tps⋆weaken : ∀ {ν n} (xs : Vec (Type ν) n) → 
                 ⟦ (map TSS.weaken xs) ⟧tps ≡ (map FTSS.weaken ⟦ xs ⟧tps)
  ⟦⟧tps⋆weaken xs = begin
    (map ⟦_⟧tp ∘ map TSS.weaken) xs
     ≡⟨ sym $ (map-∘ ⟦_⟧tp TSS.weaken) xs ⟩
    map (⟦_⟧tp ∘ TSS.weaken) xs
     ≡⟨ (map-cong weaken⋆⟦_⟧tp) xs ⟩
    map (FTSS.weaken ∘ ⟦_⟧tp) xs
     ≡⟨ (map-∘ FTSS.weaken ⟦_⟧tp) xs ⟩ 
    map FTSS.weaken (map ⟦_⟧tp xs) ∎
     
  -- the semantics of identity type-substitution is exactly 
  -- system-f's identity type substitution
  ⟦id⟧≡fid : ∀ {n} → map ⟦_⟧tp (TS.id {n}) ≡ F.id
  ⟦id⟧≡fid {zero} = refl
  ⟦id⟧≡fid {suc n} = begin
    map ⟦_⟧tp (tvar zero ∷ map TSS.weaken (TS.id {n})) 
      ≡⟨ refl ⟩
    F.tvar zero ∷ (map ⟦_⟧tp (map TSS.weaken (TS.id {n}))) 
      ≡⟨ cong (_∷_ (F.tvar zero)) (⟦⟧tps⋆weaken (TS.id {n})) ⟩
    F.tvar zero ∷ (map FTSS.weaken (map ⟦_⟧tp (TS.id {n}))) 
      ≡⟨ cong (λ e → F.tvar zero ∷ (map FTSS.weaken e)) ⟦id⟧≡fid ⟩
    F.tvar zero ∷ (map FTSS.weaken (F.id {n})) 
      ≡⟨ refl ⟩
    F.id ∎
  
  -- the semantics of type weakening is exactly system-f's type weakening
  ⟦wk⟧≡fwk : ∀ {n} → map ⟦_⟧tp (TS.wk {n}) ≡ F.wk {n}
  ⟦wk⟧≡fwk = begin
    map ⟦_⟧tp TS.wk 
      ≡⟨ ⟦⟧tps⋆weaken TS.id ⟩
    map FTSS.weaken (map ⟦_⟧tp TS.id) 
      ≡⟨ cong (map FTSS.weaken) ⟦id⟧≡fid ⟩
    F.wk ∎

  -- interpretation of contexts 
  ⟦⟧tps⋆↑ :  ∀ {ν n} (v : Vec (Type ν) n) → ⟦ v TS.↑ ⟧tps ≡ ⟦ v ⟧tps F.↑
  ⟦⟧tps⋆↑ xs = begin
    F.tvar zero ∷ (map ⟦_⟧tp (map TSS.weaken xs)) 
      ≡⟨ cong (_∷_ (F.tvar zero)) (⟦⟧tps⋆weaken xs) ⟩
    F.tvar zero ∷ (map FTSS.weaken (map ⟦_⟧tp xs)) 
      ≡⟨ refl ⟩
    (map ⟦_⟧tp xs) F.↑ ∎

  -- type substitution commutes with interpreting types
  /⋆⟦⟧tp : ∀ {ν μ} (tp : Type ν) (σ : Sub Type ν μ) → ⟦ tp TS./ σ ⟧tp ≡ ⟦ tp ⟧tp F./ (map ⟦_⟧tp σ)
  /⋆⟦⟧tp (tvar n) σ = begin
    ⟦ lookup n σ ⟧tp 
      ≡⟨ lookup⋆map σ ⟦_⟧tp n ⟩
    ⟦ tvar n ⟧tp F./ (map ⟦_⟧tp σ) ∎
  /⋆⟦⟧tp (l →' r) σ = cong₂ F._→'_ (/⋆⟦⟧tp l σ) (/⋆⟦⟧tp r σ)
  /⋆⟦⟧tp (l ⇒ r) σ = cong₂ F._→'_ (/⋆⟦⟧tp l σ) (/⋆⟦⟧tp r σ)

  -- polytype substitution commutes with interpreting types
  /⋆⟦⟧pt : ∀ {ν μ} (tp : PolyType ν) (σ : Sub Type ν μ) → ⟦ tp /tp σ ⟧pt ≡ ⟦ tp ⟧pt F./ (map ⟦_⟧tp σ)
  /⋆⟦⟧pt (mono x) σ = /⋆⟦⟧tp x σ
  /⋆⟦⟧pt (∀' tp) σ = begin
    F.∀' (⟦ tp /tp (σ TS.↑) ⟧pt) 
      ≡⟨ cong F.∀' (/⋆⟦⟧pt tp (σ TS.↑)) ⟩
    F.∀' (⟦ tp ⟧pt F./ (map ⟦_⟧tp (σ TS.↑))) 
      ≡⟨ cong (λ e → F.∀' (⟦ tp ⟧pt F./ e)) (⟦⟧tps⋆↑ σ) ⟩
    ⟦ ∀' tp ⟧pt F./ (map ⟦_⟧tp σ) ∎
  
  -- forall' application commutes with interpreting types
  ⟦sub⟧≡sub⟦⟧ : ∀ {ν} (a : PolyType (suc ν)) b → 
                ⟦ a /tp (TS.sub b) ⟧pt ≡ ⟦ a ⟧pt F./ (F.sub ⟦ b ⟧tp)
  ⟦sub⟧≡sub⟦⟧ a b = begin
      ⟦ a /tp TS.sub b ⟧pt 
        ≡⟨ /⋆⟦⟧pt a (b ∷ TS.id) ⟩
      ⟦ a ⟧pt F./ (map ⟦_⟧tp (b ∷ TS.id)) 
        ≡⟨ refl ⟩
      ⟦ a ⟧pt F./ (⟦ b ⟧tp ∷ (map ⟦_⟧tp TS.id)) 
        ≡⟨ cong (λ s → ⟦ a ⟧pt F./ (⟦ b ⟧tp ∷ s)) ⟦id⟧≡fid ⟩
      ⟦ a ⟧pt F./ (F.sub ⟦ b ⟧tp) ∎

  postulate ⟦sub⟧≡sub⟦⟧' : ∀ {ν} (a : PolyType (suc ν)) b → 
                           ⟦ a pt[/pt b ] ⟧pt ≡ ⟦ a ⟧pt F./ (F.sub ⟦ b ⟧pt)

  -- type weakening commutes with interpreting types
  weaken-pt⋆⟦⟧pt : ∀ {ν} (tp : PolyType ν) → ⟦ tp /tp TS.wk ⟧pt ≡ ⟦ tp ⟧pt F./ F.wk
  weaken-pt⋆⟦⟧pt tp = begin
    ⟦ tp /tp TS.wk ⟧pt
      ≡⟨ /⋆⟦⟧pt tp TS.wk ⟩
    ⟦ tp ⟧pt F./ (map ⟦_⟧tp TS.wk) 
      ≡⟨ cong (λ e → ⟦ tp ⟧pt F./ e) ⟦wk⟧≡fwk ⟩
    ⟦ tp ⟧pt F./ F.wk ∎

  -- context weakening commutes with interpreting contexts
  ctx-weaken⋆⟦⟧ctx : ∀ {ν n} (K : Ktx ν n) → ⟦ ktx-weaken K ⟧ctx ≡ F.ctx-weaken ⟦ K ⟧ctx
  ctx-weaken⋆⟦⟧ctx ([] , Δ) = refl
  ctx-weaken⋆⟦⟧ctx (x ∷ Γ , Δ) with ctx-weaken⋆⟦⟧ctx (Γ , Δ)
  ctx-weaken⋆⟦⟧ctx (x ∷ Γ , Δ) | ih = begin
    ⟦ ktx-weaken (x ∷ Γ , Δ) ⟧ctx ≡⟨ refl ⟩ 
    ⟦ x /tp TS.wk ⟧pt ∷ xs ≡⟨ cong (flip _∷_ xs) (weaken-pt⋆⟦⟧pt x) ⟩
    ⟦ x ⟧pt F./ F.wk ∷ ⟦ ktx-weaken (Γ , Δ) ⟧ctx ≡⟨ cong (_∷_ (⟦ x ⟧pt F./ F.wk)) ih ⟩
    ⟦ x ⟧pt F./ F.wk ∷ F.ctx-weaken ⟦ Γ , Δ ⟧ctx ≡⟨ refl ⟩
    F.ctx-weaken ⟦ x ∷ Γ , Δ ⟧ctx ∎
    where
      xs = map ⟦_⟧pt $ map (λ s → s /tp TS.wk ) Γ

open Lemmas

inst {t = t} {K = K} (mono a≡b) pt = , Prelude.subst (λ x → K F.⊢ t ∈ x) (cong ⟦_⟧tp a≡b) pt
inst {ν} {n} {a = ∀' a'} {t = t} {K = K} (poly-forall a'⊑b) wt-t = 
  , F.Λ (proj₂ $ inst a'⊑b wt-t')
  where
    t' = (F.tm-weaken t) F.[ F.tvar zero ]
    wt-t' : F.ctx-weaken K F.⊢ t' ∈ ⟦ a' ⟧pt
    wt-t' = subst 
      (λ τ → F.ctx-weaken K F.⊢ t' ∈ τ) 
      (F.TypeLemmas.a/var-wk-↑/sub-0≡a ⟦ a' ⟧pt)
      ((F.WtTypeLemmas.weaken wt-t) F.[ F.tvar zero ])
inst {ν} {n} {a = ∀' a'} {t = t} {K = K} (poly-instance c a[c]⊑b) wt-at = 
  inst a[c]⊑b wt-t[c]
  where
    t[c] : F.Term ν n
    t[c] = t F.[ ⟦ c ⟧pt ]
    -- proof that t[c] is well typed
    wt-t[c] = subst 
      (λ a′ → K F.⊢ t[c] ∈ a′) 
      {!!} -- (sym $ ⟦sub⟧≡sub⟦⟧' a' c) 
      (wt-at F.[ ⟦ c ⟧pt ])

⟦_,_⟧i {K = K} (r , p) m with first⟶∈ p 
⟦_,_⟧i {K = K} (r , p) m | r∈Δ , by-value r⊑a with ∈⟶index (All.lookup m r∈Δ)
⟦_,_⟧i {K = K} (r , p) m | r∈Δ , by-value r⊑a | i , lookup-i≡r = 
  (inst r⊑a (subst (λ τ → ⟦ K ⟧ctx F.⊢ F.var i ∈ τ) eq (F.var i)))
  where
    eq = begin 
      lookup i ⟦ K ⟧ctx 
        ≡⟨ lookup⋆⟦⟧ctx K i ⟩
      ⟦ lookup i (proj₁ K) ⟧pt
        ≡⟨ cong ⟦_⟧pt lookup-i≡r ⟩
      ⟦ r ⟧pt ∎ 
⟦_,_⟧i {K = K} (r , p) m | r∈Δ , yields Δ↝b r⊑b⇒a with ∈⟶index (All.lookup m r∈Δ)
⟦_,_⟧i {K = K} (r , p) m | r∈Δ , yields Δ↝b r⊑b⇒a | i , lookup-i≡r = 
  , (rule-inst F.· (proj₂ ⟦ Δ↝b , m ⟧i))
  where
    eq = begin 
      lookup i ⟦ K ⟧ctx
        ≡⟨ lookup⋆⟦⟧ctx K i ⟩
      ⟦ lookup i (proj₁ K) ⟧pt
        ≡⟨ cong ⟦_⟧pt lookup-i≡r ⟩
      ⟦ r ⟧pt ∎ 
    rule-inst = proj₂ (inst r⊑b⇒a (subst (λ τ → ⟦ K ⟧ctx F.⊢ F.var i ∈ τ) eq (F.var i)))

-- interpretation of well-typed terms in System F preserves type
⟦⟧-preserves-tp : ∀ {ν n} {K : Ktx ν n} {t a} → (wt-t : K ⊢ t ∈ a) → (m : K# K) →
                  ⟦ K ⟧ctx F.⊢ ⟦ wt-t , m ⟧ ∈ ⟦ a ⟧pt
⟦⟧-preserves-tp {K = K} (var x) m = subst-wt-var (lookup⋆⟦⟧ctx K x) (F.var x)
  where
    subst-wt-var = subst (λ a → ⟦ K ⟧ctx F.⊢ (F.var x) ∈ a)
⟦⟧-preserves-tp {K = K} {a = ∀' a} (Λ wt-e) m with ⟦⟧-preserves-tp wt-e (#tvar m)
... | ih = F.Λ (subst-wt-ctx (ctx-weaken⋆⟦⟧ctx K) ih)
  where
    subst-wt-ctx = subst (λ c → c F.⊢ ⟦ wt-e , #tvar m ⟧ ∈ ⟦ a ⟧pt)
⟦⟧-preserves-tp (λ' a wt-e) m with ⟦⟧-preserves-tp wt-e (#var (mono a) m)
⟦⟧-preserves-tp (λ' a wt-e) m | ih = F.λ' ⟦ a ⟧tp ih
⟦⟧-preserves-tp {K = K} (_[_] {a = a} wt-tc b) m with ⟦⟧-preserves-tp wt-tc m
... | ih = subst-tp (sym $ ⟦sub⟧≡sub⟦⟧ a b) (ih F.[ ⟦ b ⟧tp ])
  where
    subst-tp = subst (λ c → ⟦ K ⟧ctx F.⊢ ⟦ wt-tc [ b ] , m ⟧ ∈ c) 
⟦⟧-preserves-tp (wt-f · wt-e) m with ⟦⟧-preserves-tp wt-f m | ⟦⟧-preserves-tp wt-e m
⟦⟧-preserves-tp (wt-f · wt-e) m | ih | y = ih F.· y
⟦⟧-preserves-tp (ρ a wt-e) m with ⟦⟧-preserves-tp wt-e (#ivar (mono a) m)
⟦⟧-preserves-tp (ρ a wt-e) m | ih = F.λ' ⟦ a ⟧tp ih
⟦⟧-preserves-tp (_⟨⟩ wt-r e) m with ⟦⟧-preserves-tp wt-r m
⟦⟧-preserves-tp (_⟨⟩ wt-r e) m | f-wt-r = f-wt-r F.· (proj₂ ⟦ e , m ⟧i)
⟦⟧-preserves-tp (let'_in'_ {a = a} wt-e₁ wt-e₂) m with ⟦⟧-preserves-tp wt-e₁ m | ⟦⟧-preserves-tp wt-e₂ (#var a m)
⟦⟧-preserves-tp (let'_in'_ {a = a} wt-e₁ wt-e₂) m | ih | y = (F.λ' ⟦ a ⟧pt y) F.· ih
⟦⟧-preserves-tp (implicit_in'_ {a = a} wt-e₁ wt-e₂) m with ⟦⟧-preserves-tp wt-e₁ m | ⟦⟧-preserves-tp wt-e₂ (#ivar a m)
⟦⟧-preserves-tp (implicit_in'_ {a = a} wt-e₁ wt-e₂) m | ih | y = (F.λ' ⟦ a ⟧pt y) F.· ih
