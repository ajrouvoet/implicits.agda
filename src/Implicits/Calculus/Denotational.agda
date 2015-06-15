{-# OPTIONS --no-termination-check #-}
module Implicits.Calculus.Denotational where

open import Prelude

open import Implicits.Calculus.WellTyped
open import Implicits.SystemF as F using ()
open import Extensions.ListFirst
open import Data.Fin.Substitution
open import Data.Vec.Properties

private
  module TS = TypeSubst
  open PTypeSubst
  
  module TSS = Simple TS.simple
  module FTSS = Simple F.simple

-- this is provable (see Sandro's System-F implementation)
postulate weaken-preserves-⊢ : ∀ {ν n} {K : F.Ctx ν n} {t a} → 
                               K F.⊢ t ∈ a → F.ctx-weaken K F.⊢ F.tm-weaken t ∈ F.tp-weaken a

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

-- construct an System F term from an implicit resolution
⟦_⟧i : ∀ {ν n} {K : Ktx ν n} {a} → K Δ↝ a → F.Term ν n

⟦_⟧ : ∀ {ν n} {K : Ktx ν n} {t} {a : PolyType ν} → K ⊢ t ∈ a → F.Term ν n
⟦_⟧ (var x) = F.var x
⟦_⟧ (Λ t) = F.Λ ⟦ t ⟧
⟦_⟧ (λ' a x) = F.λ' ⟦ a ⟧tp ⟦ x ⟧
⟦_⟧ (f [ b ]) = F._[_] ⟦ f ⟧ ⟦ b ⟧tp
⟦_⟧ (f · e) = ⟦ f ⟧ F.· ⟦ e ⟧
⟦_⟧ (ρ a x) = F.λ' ⟦ a ⟧tp ⟦ x ⟧
⟦_⟧ (_⟨⟩ f e∈Δ) = ⟦ f ⟧ F.· ⟦ e∈Δ ⟧i
⟦_⟧ (let'_in'_ {a = a} t e) = (F.λ' ⟦ a ⟧pt ⟦ e ⟧) F.· ⟦ t ⟧
⟦_⟧ (implicit_in'_ {a = a} t e) = (F.λ' ⟦ a ⟧pt ⟦ e ⟧) F.· ⟦ t ⟧

module Lemmas where

  -- lookup in and interpreted context Γ is equivalent to interpreting a type, looked up in K
  lookup⋆⟦⟧ctx : ∀ {ν n} (K : Ktx ν n) x → lookup x ⟦ K ⟧ctx ≡ ⟦ lookup x $ proj₁ K ⟧pt
  lookup⋆⟦⟧ctx K x = sym $ lookup⋆map (proj₁ K) ⟦_⟧pt x

  -- implicitly constructed F-terms preserve type
  postulate ⟦⟧i-wt-lemma : ∀ {ν n} {K : Ktx ν n} {a} (i : K Δ↝ a) → ⟦ K ⟧ctx F.⊢ ⟦ i ⟧i ∈ ⟦ a ⟧pt

  -- type in type substitution commutes with type interpretation
  postulate tp/tp⋆⟦⟧ctx : ∀ {ν} (a : PolyType (suc ν)) b → ⟦ a ptp[/tp b ] ⟧pt ≡ ⟦ a ⟧pt F.tp[/tp ⟦ b ⟧tp ]

  postulate weaken⋆⟦_⟧tp : ∀ {ν} → _≗_ {A = Type ν} (⟦_⟧tp ∘ TSS.weaken) (FTSS.weaken ∘ ⟦_⟧tp)

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
  /⋆⟦⟧pt : ∀ {ν μ} (tp : PolyType ν) (σ : Sub Type ν μ) → ⟦ tp / σ ⟧pt ≡ ⟦ tp ⟧pt F./ (map ⟦_⟧tp σ)
  /⋆⟦⟧pt (mono x) σ = /⋆⟦⟧tp x σ
  /⋆⟦⟧pt (∀' tp) σ = begin
    F.∀' (⟦ tp / (σ TS.↑) ⟧pt) 
      ≡⟨ cong F.∀' (/⋆⟦⟧pt tp (σ TS.↑)) ⟩
    F.∀' (⟦ tp ⟧pt F./ (map ⟦_⟧tp (σ TS.↑))) 
      ≡⟨ cong (λ e → F.∀' (⟦ tp ⟧pt F./ e)) (⟦⟧tps⋆↑ σ) ⟩
    ⟦ ∀' tp ⟧pt F./ (map ⟦_⟧tp σ) ∎
  
  -- forall' application commutes with interpreting types
  ⟦sub⟧≡sub⟦⟧ : ∀ {ν} (a : PolyType (suc ν)) b → 
                ⟦ a / (TS.sub b) ⟧pt ≡ ⟦ a ⟧pt F./ (F.sub ⟦ b ⟧tp)
  ⟦sub⟧≡sub⟦⟧ a b = begin
      ⟦ a / TS.sub b ⟧pt ≡⟨ /⋆⟦⟧pt a (b ∷ TS.id) ⟩
      ⟦ a ⟧pt F./ (map ⟦_⟧tp (b ∷ TS.id)) ≡⟨ refl ⟩
      ⟦ a ⟧pt F./ (⟦ b ⟧tp ∷ (map ⟦_⟧tp TS.id)) ≡⟨ cong (λ s → ⟦ a ⟧pt F./ (⟦ b ⟧tp ∷ s)) ⟦id⟧≡fid ⟩
      ⟦ a ⟧pt F./ (F.sub ⟦ b ⟧tp) ∎

  -- type weakening commutes with interpreting types
  {-
  weaken-tp⋆⟦⟧tp : ∀ {ν} (tp : Type ν) → ⟦ tp TS./ TS.wk ⟧tp ≡ ⟦ tp ⟧tp F./ F.wk
  weaken-tp⋆⟦⟧tp tp = begin
    ⟦ tp TS./ TS.wk ⟧tp 
      ≡⟨ /⋆⟦⟧tp tp TS.wk ⟩
    ⟦ tp ⟧tp F./ (map ⟦_⟧tp TS.wk) 
      ≡⟨ cong (λ e → ⟦ tp ⟧tp F./ e) ⟦wk⟧≡fwk ⟩
    ⟦ tp ⟧tp F./ F.wk ∎
  -}

  -- type weakening commutes with interpreting types
  weaken-pt⋆⟦⟧pt : ∀ {ν} (tp : PolyType ν) → ⟦ tp / TS.wk ⟧pt ≡ ⟦ tp ⟧pt F./ F.wk
  weaken-pt⋆⟦⟧pt tp = begin
    ⟦ tp / TS.wk ⟧pt
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
    ⟦ x / TS.wk ⟧pt ∷ xs ≡⟨ cong (flip _∷_ xs) (weaken-pt⋆⟦⟧pt x) ⟩
    ⟦ x ⟧pt F./ F.wk ∷ ⟦ ktx-weaken (Γ , Δ) ⟧ctx ≡⟨ cong (_∷_ (⟦ x ⟧pt F./ F.wk)) ih ⟩
    ⟦ x ⟧pt F./ F.wk ∷ F.ctx-weaken ⟦ Γ , Δ ⟧ctx ≡⟨ refl ⟩
    F.ctx-weaken ⟦ x ∷ Γ , Δ ⟧ctx ∎
    where
      xs = map ⟦_⟧pt $ map (λ s → s / TS.wk ) Γ

open Lemmas

{-
-- given a proof that type a is a specialization of type b
-- and a term of type a, we can build a term of type b
inst : ∀ {ν n} {a b : PolyType ν} {K : Ktx ν n} → a ⊑ b → 
               ∀ {t} → K ⊢ t ∈ a → ∃ λ t' → K ⊢ t' ∈ b
inst {K = K} (mono x) {t = t} pt = , Prelude.subst (λ x → K ⊢ t ∈ mono x) x pt
inst {ν} {n} {a = ∀' a'} {K = K} (poly-forall a'⊑b) {t} wt = 
  let t'' , wt'' = inst a'⊑b wt' in , Λ wt''
  where
    t' = (tm-weaken t) [ tvar Fin.zero ]
    eq : (a' ptp/tp (TS.wk TS.↑)) ptp/tp (TS.sub (tvar Fin.zero)) ≡ a'
    eq = begin
      (a' ptp/tp (TS.wk TS.↑)) ptp/tp (TS.sub (tvar zero)) ≡⟨ refl ⟩
      (a' ptp/tp ((tvar zero) ∷ map TSS.weaken TS.wk)) ptp/tp ((tvar zero) ∷ TS.id) ≡⟨ {!!} ⟩
      a' ptp/tp (((tvar zero) ∷ map TSS.weaken TS.wk) TS.⊙ ((tvar zero) ∷ TS.id)) ≡⟨ {!!} ⟩
      (a' ptp/tp TS.id) ≡⟨ {!!} ⟩
      a' ∎
    wt' : ktx-weaken K ⊢ t' ∈ a'
    wt' = subst (λ τ → ktx-weaken K ⊢ t' ∈ τ) eq ((weaken-preserves-⊢ wt) [ tvar Fin.zero ])
inst (poly-instance {c = c} a[c]⊑b) wt-a = inst a[c]⊑b (wt-a [ c ])
-}

-- given a proof that some calculus type b is a specialization of a,
-- and an F-instance of a, we can build an F-instance of b
-- (it might seem more natural to first build a Calculus term and keep the interpretation out of this,
--    but that gives termination checking problems, since we could put more implicit applications in the 
--    constructed term)
inst : ∀ {ν n} {a b t} {K : F.Ctx ν n} → a ⊑ b → K F.⊢ t ∈ ⟦ a ⟧pt → ∃ λ t' → K F.⊢ t' ∈ ⟦ b ⟧pt
inst {t = t} {K = K} (mono a≡b) pt = , Prelude.subst (λ x → K F.⊢ t ∈ x) (cong ⟦_⟧tp a≡b) pt
inst {ν} {n} {a = ∀' a'} {t = t} {K = K} (poly-forall a'⊑b) wt-t = 
  , F.Λ (proj₂ $ inst a'⊑b wt-t')
  where
    t' = (F.tm-weaken t) F.[ F.tvar zero ]
    wt-t' : F.ctx-weaken K F.⊢ t' ∈ ⟦ a' ⟧pt
    wt-t' = subst 
      (λ τ → F.ctx-weaken K F.⊢ t' ∈ τ) 
      (F.TypeLemmas.a/var-wk-↑/sub-0≡a ⟦ a' ⟧pt)
      ((weaken-preserves-⊢ wt-t) F.[ F.tvar zero ])
inst {ν} {n} {a = ∀' a'} {t = t} {K = K} (poly-instance {c = c} a[c]⊑b) wt-at = 
  inst a[c]⊑b wt-t[c]
  where
    t[c] : F.Term ν n
    t[c] = t F.[ ⟦ c ⟧tp ]
    wt-t[c] = subst (λ a′ → K F.⊢ t F.[ ⟦ c ⟧tp ] ∈ a′) (sym $ ⟦sub⟧≡sub⟦⟧ a' c) (wt-at F.[ ⟦ c ⟧tp ])

⟦_⟧i {ν} {n} {K} (r , p) with first⟶witness p
⟦_⟧i {ν} {n} {K} (r , p) | by-value r⊑a = proj₁ (inst r⊑a rt)
  where
    -- somehow we have to pick up this one from the explicit context
    postulate t : F.Term ν n 
    postulate rt : ⟦ K ⟧ctx F.⊢ t ∈ ⟦ r ⟧pt
⟦_⟧i {ν} {n} {K} (r , p) | yields {a = a} K↝a r⊑a⇒b with ⟦ K↝a ⟧i
⟦_⟧i {ν} {n} {K} (r , p) | yields {a = a} K↝a r⊑a⇒b | tm-a = tm-rule-inst F.· tm-a
  where
    -- somehow we have to pick up this one from the explicit context
    postulate t : F.Term ν n 
    postulate rt : ⟦ K ⟧ctx F.⊢ t ∈ ⟦ r ⟧pt 
    tm-rule-inst = proj₁ (inst r⊑a⇒b rt)

-- interpretation of well-typed terms in System F preserves type
⟦⟧-preserves-tp : ∀ {ν n} {K : Ktx ν n} {t a} → (wt-t : K ⊢ t ∈ a) → ⟦ K ⟧ctx F.⊢ ⟦ wt-t ⟧ ∈ ⟦ a ⟧pt
⟦⟧-preserves-tp {K = K} (var x) = subst-wt-var (lookup⋆⟦⟧ctx K x) (F.var x)
  where
    subst-wt-var = subst (λ a → ⟦ K ⟧ctx F.⊢ (F.var x) ∈ a)
⟦⟧-preserves-tp {K = K} {a = ∀' a} (Λ wt-e) with ⟦⟧-preserves-tp wt-e 
... | f-wt-e = F.Λ (subst-wt-ctx (ctx-weaken⋆⟦⟧ctx K) f-wt-e)
  where
    subst-wt-ctx = subst (λ c → c F.⊢ ⟦ wt-e ⟧ ∈ ⟦ a ⟧pt)
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
⟦⟧-preserves-tp (let' wt-e₁ in' wt-e₂) with ⟦⟧-preserves-tp wt-e₁ | ⟦⟧-preserves-tp wt-e₂
⟦⟧-preserves-tp (let'_in'_ {a = a} wt-e₁ wt-e₂) | x | y = (F.λ' ⟦ a ⟧pt y) F.· x
⟦⟧-preserves-tp (implicit wt-e₁ in' wt-e₂) with ⟦⟧-preserves-tp wt-e₁ | ⟦⟧-preserves-tp wt-e₂
⟦⟧-preserves-tp (implicit_in'_ {a = a} wt-e₁ wt-e₂) | x | y = (F.λ' ⟦ a ⟧pt y) F.· x
