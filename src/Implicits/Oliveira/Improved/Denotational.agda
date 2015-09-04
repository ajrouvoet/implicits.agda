open import Prelude

module Implicits.Oliveira.Improved.Denotational
  (TC : Set)
  (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Implicits.Oliveira.Types TC _tc≟_
open import Implicits.Oliveira.Terms TC _tc≟_
open import Implicits.Oliveira.Contexts TC _tc≟_
open import Implicits.Oliveira.WellTyped TC _tc≟_
open import Implicits.Oliveira.Substitutions TC _tc≟_
open import Implicits.Oliveira.Substitutions.Lemmas TC _tc≟_
open import Implicits.Oliveira.Improved.Resolution TC _tc≟_
open import Implicits.SystemF TC as F using ()
open import Extensions.ListFirst
open import Data.Fin.Substitution
open import Data.Vec.Properties

open TypingRules _⊢ᵣ_
open SubstLemmas _⊢ᵣ_

module RewriteContext where

  -- rewrite context (relation between implicit and explicit context)
  K# : ∀ {ν n : ℕ} (K : Ktx ν n) → Set
  K# (Γ , Δ) = All (λ i → i ∈ Γ) Δ
  
  #tvar : ∀ {ν n} {K : Ktx ν n} → K# K → K# (ktx-weaken K)
  #tvar All.[] = All.[]
  #tvar (px All.∷ K#K) = (∈⋆map px (λ t → t tp/tp TypeLemmas.wk)) All.∷ (#tvar K#K)

  #var : ∀ {ν n} {K : Ktx ν n} → (a : Type ν) → K# K → K# (a ∷Γ K)
  #var a All.[] = All.[]
  #var a (px All.∷ K#K) = there px All.∷ (#var a K#K)

  #ivar : ∀ {ν n} {K : Ktx ν n} → (a : Type ν) → K# K → K# (a ∷K K)
  #ivar a K#K = here All.∷ (All.map there K#K)

private
  module TS = TypeLemmas
  open RewriteContext
  
mutual
  ⟦_⟧stp : ∀ {ν} → SimpleType ν → F.Type ν
  ⟦ tc c ⟧stp = F.tc c
  ⟦ tvar n ⟧stp = F.tvar n
  ⟦ a →' b ⟧stp = ⟦ a ⟧tp F.→' ⟦ b ⟧tp

  ⟦_⟧tp : ∀ {ν} → Type ν → F.Type ν
  ⟦ simpl x ⟧tp = ⟦ x ⟧stp 
  ⟦ a ⇒ b ⟧tp = ⟦ a ⟧tp F.→' ⟦ b ⟧tp
  ⟦ ∀' x ⟧tp = F.∀' ⟦ x ⟧tp

⟦_⟧tps : ∀ {ν n} → Vec (Type ν) n → Vec (F.Type ν) n
⟦ v ⟧tps = map (⟦_⟧tp) v

⟦_⟧ctx : ∀ {ν n} → Ktx ν n → F.Ctx ν n
⟦ Γ , Δ ⟧ctx = map ⟦_⟧tp Γ

-- construct an System F term from an implicit resolution
⟦_,_⟧r : ∀ {ν n} {K : Ktx ν n} {a} → K ⊢ᵣ a → K# K → ∃ λ t → ⟦ K ⟧ctx F.⊢ t ∈ ⟦ a ⟧tp

-- denotational semantics of well-typed terms
⟦_,_⟧t : ∀ {ν n} {K : Ktx ν n} {t} {a : Type ν} → K ⊢ t ∈ a → K# K → F.Term ν n
⟦_,_⟧t (new c) m = F.new c
⟦_,_⟧t (var x) m = F.var x
⟦_,_⟧t (Λ t) m = F.Λ ⟦ t , #tvar m ⟧t
⟦_,_⟧t (λ' a x) m = F.λ' ⟦ a ⟧tp ⟦ x , #var a m ⟧t
⟦_,_⟧t (f [ b ]) m = F._[_] ⟦ f , m ⟧t ⟦ b ⟧tp
⟦_,_⟧t (f · e) m = ⟦ f , m ⟧t F.· ⟦ e , m ⟧t
⟦_,_⟧t (ρ {a = a} unamb-a x) m = F.λ' ⟦ a ⟧tp ⟦ x , #ivar a m ⟧t
⟦_,_⟧t (f ⟨ e ⟩) m = ⟦ f , m ⟧t F.· ⟦ e , m ⟧t
⟦_,_⟧t (¿ unamb-a K⊢ᵣa) m = proj₁ ⟦ K⊢ᵣa , m ⟧r
⟦_,_⟧t (let'_in'_ {a = a} t e) m = (F.λ' ⟦ a ⟧tp ⟦ e , #var a m ⟧t) F.· ⟦ t , m ⟧t
⟦_,_⟧t (implicit_in'_ {a = a} t e) m = (F.λ' ⟦ a ⟧tp ⟦ e , #ivar a m ⟧t) F.· ⟦ t , m ⟧t

module Lemmas where
  ⟦a/var⟧≡⟦a⟧/var : ∀ {n m} a (σ : Sub Fin n m) → ⟦ a TS./Var σ ⟧tp ≡ ⟦ a ⟧tp F./Var σ
  ⟦a/var⟧≡⟦a⟧/var (simpl (tc x)) σ = refl
  ⟦a/var⟧≡⟦a⟧/var (simpl (tvar n)) σ = refl
  ⟦a/var⟧≡⟦a⟧/var (simpl (a →' b)) σ = cong₂ F._→'_ (⟦a/var⟧≡⟦a⟧/var a σ) (⟦a/var⟧≡⟦a⟧/var b σ)
  ⟦a/var⟧≡⟦a⟧/var (a ⇒ b) σ = cong₂ F._→'_ (⟦a/var⟧≡⟦a⟧/var a σ) (⟦a/var⟧≡⟦a⟧/var b σ)
  ⟦a/var⟧≡⟦a⟧/var (∀' a) σ = cong F.∀' (⟦a/var⟧≡⟦a⟧/var a (σ TS.Var.↑))

  ⟦weaken⟧≡fweaken : ∀ {ν} (a : Type ν) → ⟦ TS.weaken a ⟧tp ≡ F.weaken ⟦ a ⟧tp
  ⟦weaken⟧≡fweaken x = begin
    ⟦ x TS./Var (TS.Var.wk) ⟧tp
      ≡⟨ (⟦a/var⟧≡⟦a⟧/var x (TS.Var.wk)) ⟩
    F.weaken ⟦ x ⟧tp ∎

  ⟦map-weaken⟧≡map-fweaken : ∀ {m n} (xs : Sub Type m n) → ⟦ map TS.weaken xs ⟧tps ≡ map F.weaken ⟦ xs ⟧tps
  ⟦map-weaken⟧≡map-fweaken xs = begin 
    (map ⟦_⟧tp ∘ map TS.weaken) xs
        ≡⟨ sym $ map-∘ ⟦_⟧tp TS.weaken xs ⟩
    map (⟦_⟧tp ∘ TS.weaken) xs
        ≡⟨ map-cong ⟦weaken⟧≡fweaken xs ⟩
    map (F.weaken ∘ ⟦_⟧tp) xs
        ≡⟨ map-∘ F.weaken ⟦_⟧tp xs ⟩ 
    map F.weaken (map ⟦_⟧tp xs) ∎

  ⟦σ↑⟧≡⟦σ⟧↑ : ∀ {ν μ} (σ : Sub Type ν μ) → ⟦ σ TS.↑ ⟧tps ≡ ⟦ σ ⟧tps F.↑
  ⟦σ↑⟧≡⟦σ⟧↑ σ = begin
    (F.tvar zero) ∷ ⟦ map TS.weaken σ ⟧tps
      ≡⟨ cong (λ u → (F.tvar zero) ∷ u) (⟦map-weaken⟧≡map-fweaken σ) ⟩
    (F.tvar zero) ∷ map F.weaken ⟦ σ ⟧tps
      ≡⟨ refl ⟩
    ⟦ σ ⟧tps F.↑ ∎
  
  ⟦id⟧≡fid : ∀ {n} → ⟦ TS.id {n} ⟧tps ≡ F.id {n}
  ⟦id⟧≡fid {zero} = refl
  ⟦id⟧≡fid {suc n} = begin
    F.tvar zero ∷ (map ⟦_⟧tp (map TS.weaken TS.id)) 
      ≡⟨ cong (_∷_ (F.tvar zero)) (⟦map-weaken⟧≡map-fweaken TS.id) ⟩
    F.tvar zero ∷ (map F.weaken (map ⟦_⟧tp TS.id)) 
      ≡⟨ cong (λ e → F.tvar zero ∷ (map F.weaken e)) ⟦id⟧≡fid ⟩
    F.tvar zero ∷ (map F.weaken F.id) 
      ≡⟨ refl ⟩
    F.id ∎
  
  ⟦wk⟧≡fwk : ∀ {n} → ⟦ TS.wk {n} ⟧tps ≡ F.wk {n}
  ⟦wk⟧≡fwk = begin
    map ⟦_⟧tp TS.wk 
      ≡⟨ ⟦map-weaken⟧≡map-fweaken TS.id ⟩
    map F.weaken (map ⟦_⟧tp TS.id) 
      ≡⟨ cong (map F.weaken) ⟦id⟧≡fid ⟩
    F.wk ∎

  -- lookup in and interpreted context Γ is equivalent to interpreting a type, looked up in K
  ⟦lookup-ctx⟧≡lookup-⟦ctx⟧ : ∀ {ν n} (K : Ktx ν n) x → lookup x ⟦ K ⟧ctx ≡ ⟦ lookup x $ proj₁ K ⟧tp
  ⟦lookup-ctx⟧≡lookup-⟦ctx⟧ K x = sym $ lookup⋆map (proj₁ K) ⟦_⟧tp x

  -- type substitution commutes with interpreting types
  ⟦a/s⟧≡⟦a⟧/⟦s⟧ : ∀ {ν μ} (tp : Type ν) (σ : Sub Type ν μ) → ⟦ tp tp/tp σ ⟧tp ≡ ⟦ tp ⟧tp F./ ⟦ σ ⟧tps
  ⟦a/s⟧≡⟦a⟧/⟦s⟧ (simpl (tc c)) σ = refl
  ⟦a/s⟧≡⟦a⟧/⟦s⟧ (simpl (tvar n)) σ = begin
    ⟦ lookup n σ ⟧tp 
      ≡⟨ lookup⋆map σ ⟦_⟧tp n ⟩
    ⟦ simpl $ tvar n ⟧tp F./ (map ⟦_⟧tp σ) ∎
  ⟦a/s⟧≡⟦a⟧/⟦s⟧ (simpl (l →' r)) σ = cong₂ F._→'_ (⟦a/s⟧≡⟦a⟧/⟦s⟧ l σ) (⟦a/s⟧≡⟦a⟧/⟦s⟧ r σ)
  ⟦a/s⟧≡⟦a⟧/⟦s⟧ (l ⇒ r) σ = cong₂ F._→'_ (⟦a/s⟧≡⟦a⟧/⟦s⟧ l σ) (⟦a/s⟧≡⟦a⟧/⟦s⟧ r σ)
  ⟦a/s⟧≡⟦a⟧/⟦s⟧ (∀' a) σ = begin
    F.∀' ⟦ (a TS./ σ TS.↑) ⟧tp
      ≡⟨ cong F.∀' (⟦a/s⟧≡⟦a⟧/⟦s⟧ a (σ TS.↑)) ⟩
    F.∀' (⟦ a ⟧tp F./ ⟦ σ TS.↑ ⟧tps)
      ≡⟨ cong (λ u → F.∀' (⟦ a ⟧tp F./ u)) ((⟦σ↑⟧≡⟦σ⟧↑ σ)) ⟩
    ⟦ ∀' a ⟧tp F./ (map ⟦_⟧tp σ) ∎

  -- forall' application commutes with interpreting types
  ⟦sub⟧≡sub : ∀ {ν} (a : Type (suc ν)) b → ⟦ a tp/tp (TS.sub b) ⟧tp ≡ ⟦ a ⟧tp F./ (F.sub ⟦ b ⟧tp)
  ⟦sub⟧≡sub a b = begin
    ⟦ a tp/tp (TS.sub b) ⟧tp
    ≡⟨ ⟦a/s⟧≡⟦a⟧/⟦s⟧ a (b ∷ TS.id) ⟩
    (⟦ a ⟧tp F./ (map ⟦_⟧tp (b ∷ TS.id)) )
    ≡⟨ refl ⟩
    (⟦ a ⟧tp F./ (⟦ b ⟧tp ∷ (map ⟦_⟧tp TS.id)) )
    ≡⟨ cong (λ s → ⟦ a ⟧tp F./ (⟦ b ⟧tp ∷ s)) ⟦id⟧≡fid ⟩
    (⟦ a ⟧tp F./ (F.sub ⟦ b ⟧tp)) ∎

  ⟦/wk⟧≡/wk : ∀ {ν} (tp : Type ν) → ⟦ tp tp/tp TS.wk ⟧tp ≡ ⟦ tp ⟧tp F./ F.wk
  ⟦/wk⟧≡/wk tp = begin
    ⟦ tp tp/tp TS.wk ⟧tp
      ≡⟨ ⟦a/s⟧≡⟦a⟧/⟦s⟧ tp TS.wk ⟩
    ⟦ tp ⟧tp F./ (map ⟦_⟧tp TS.wk) 
      ≡⟨ cong (λ e → ⟦ tp ⟧tp F./ e) ⟦wk⟧≡fwk ⟩
    ⟦ tp ⟧tp F./ F.wk ∎

  -- context weakening commutes with interpreting contexts
  ⟦ctx-weaken⟧≡ctx-weaken : ∀ {ν n} (K : Ktx ν n) → ⟦ ktx-weaken K ⟧ctx ≡ F.ctx-weaken ⟦ K ⟧ctx
  ⟦ctx-weaken⟧≡ctx-weaken ([] , Δ) = refl
  ⟦ctx-weaken⟧≡ctx-weaken (x ∷ Γ , Δ) with ⟦ctx-weaken⟧≡ctx-weaken (Γ , Δ)
  ⟦ctx-weaken⟧≡ctx-weaken (x ∷ Γ , Δ) | ih = begin
    ⟦ ktx-weaken (x ∷ Γ , Δ) ⟧ctx ≡⟨ refl ⟩ 
    ⟦ x tp/tp TS.wk ⟧tp ∷ xs ≡⟨ cong (flip _∷_ xs) (⟦/wk⟧≡/wk x) ⟩
    (⟦ x ⟧tp F./ F.wk) ∷ ⟦ ktx-weaken (Γ , Δ) ⟧ctx ≡⟨ cong (_∷_ (⟦ x ⟧tp F./ F.wk)) ih ⟩
    (⟦ x ⟧tp F./ F.wk) ∷ F.ctx-weaken ⟦ Γ , Δ ⟧ctx ≡⟨ refl ⟩
    F.ctx-weaken ⟦ x ∷ Γ , Δ ⟧ctx ∎
    where
      xs = map ⟦_⟧tp $ map (λ s → s tp/tp TS.wk ) Γ

  open Rules

  -- polymorphic rules, translate to polymorphic functions
  ⟦rule⟧⟶function : ∀ {ν} {a : Type ν} → IsRule a → F.IsFunction ⟦ a ⟧tp
  ⟦rule⟧⟶function (rule a b) = F.lambda ⟦ a ⟧tp ⟦ b ⟧tp
  ⟦rule⟧⟶function (∀'-rule r) = F.∀'-lambda (⟦rule⟧⟶function r)

  -- using the above definition of rule translation
  -- we can prove that codomains of rules translate to codomains of functions
  rule-codomain⋆⟦⟧ : ∀ {ν} {a : Type ν} → (r : IsRule a) →
                     ⟦ codomain r ⟧tp ≡ F.codomain (⟦rule⟧⟶function r)
  rule-codomain⋆⟦⟧ (rule a b) = refl
  rule-codomain⋆⟦⟧ (∀'-rule r) = cong F.∀' (rule-codomain⋆⟦⟧ r)

  -- using the above definition of rule translation
  -- we can prove that the domains of rules translate to the domains of functions
  rule-domain⋆⟦⟧ : ∀ {ν} {a : Type ν} → (r : IsRule a) →
                   ⟦ domain r ⟧tp ≡ F.domain (⟦rule⟧⟶function r)
  rule-domain⋆⟦⟧ (rule a b) = refl
  rule-domain⋆⟦⟧ (∀'-rule r) = cong F.∀' (rule-domain⋆⟦⟧ r)

  -- finally we can prove that we can build a instance in the codomain of a polymorphic rule
  -- from an instance of the rule and an instance in its domain
  poly-· : ∀ {ν n} {a} {Γ : F.Ctx ν n} {f t} →
           (ρ : IsRule a) → Γ F.⊢ f ∈ ⟦ a ⟧tp → Γ F.⊢ t ∈ ⟦ domain ρ ⟧tp →
           ∃ λ t' → Γ F.⊢ t' ∈ ⟦ codomain ρ ⟧tp
  poly-· {Γ = Γ} a-rule ⊢f ⊢arg =
    , subst (λ u → Γ F.⊢ proj₁ ⊢t ∈ u) (sym $ rule-codomain⋆⟦⟧ a-rule) (proj₂ ⊢t)
    where
      ⊢t = F.poly-·
             (⟦rule⟧⟶function a-rule) ⊢f -- function
             (subst (λ u → Γ F.⊢ _ ∈ u) (rule-domain⋆⟦⟧ a-rule) ⊢arg) -- argument

open Lemmas

inst↓ : ∀ {ν n} {K : Ktx ν n} {r t a} → K ⊢ r ↓ a → ⟦ K ⟧ctx F.⊢ t ∈ ⟦ r ⟧tp → K# K →
       ∃ λ e → ⟦ K ⟧ctx F.⊢ e ∈ ⟦ a ⟧stp
inst↓ {K = K} (i-simp a) ⊢a m = , ⊢a
inst↓ {K = K} (i-iabs ⊢ra a↓b) ⊢a m = inst↓ a↓b (⊢a F.· (proj₂ ⟦ ⊢ra , m ⟧r)) m
inst↓ {K = K} (i-tabs {ρ = r} b r[b]↓a) ⊢r m =
    inst↓ r[b]↓a (
      subst
        (λ u → ⟦ K ⟧ctx F.⊢ _ ∈ u)
        (sym $ ⟦sub⟧≡sub r b)
        (⊢r F.[ ⟦ b ⟧tp ])) m

-- declared above as:
-- ⟦_,_⟧r : ∀ {ν n} {K : Ktx ν n} {a} → K ⊢ᵣ a → K# K → ∃ λ t → ⟦ K ⟧ctx F.⊢ t ∈ ⟦ a ⟧tp
⟦_,_⟧r (r-iabs a ⊢rb) m = , F.λ' ⟦ a ⟧tp (proj₂ (⟦ ⊢rb , #ivar a m ⟧r))
⟦_,_⟧r {K = K } (r-tabs ⊢ra) m =
  , F.Λ (subst (λ K₁ → K₁ F.⊢ proj₁ ⊢body ∈ _) (⟦ctx-weaken⟧≡ctx-weaken K) (proj₂ ⊢body))
  where
    ⊢body = ⟦ ⊢ra , #tvar m ⟧r
⟦_,_⟧r {K = K} (r-simp K⟨a⟩=r) m with first⟶∈ K⟨a⟩=r
⟦_,_⟧r {K = K} (r-simp K⟨a⟩=r) m | r∈Δ , r↓a with ∈⟶index (All.lookup m r∈Δ)
⟦_,_⟧r {K = K} (r-simp {ρ = r} K⟨a⟩=r) m | r∈Δ , r↓a | i , lookup-i≡r =
  inst↓ r↓a (subst (λ τ → ⟦ K ⟧ctx F.⊢ F.var i ∈ τ) eq (F.var i)) m
  where
    eq = begin 
      lookup i ⟦ K ⟧ctx 
        ≡⟨ ⟦lookup-ctx⟧≡lookup-⟦ctx⟧ K i ⟩
      ⟦ lookup i (proj₁ K) ⟧tp
        ≡⟨ cong ⟦_⟧tp lookup-i≡r ⟩
      ⟦ r ⟧tp ∎ 

-- interpretation of well-typed terms in System F preserves type
⟦_,_⟧ : ∀ {ν n} {K : Ktx ν n} {t a} → (wt-t : K ⊢ t ∈ a) → (m : K# K) →
        ⟦ K ⟧ctx F.⊢ ⟦ wt-t , m ⟧t ∈ ⟦ a ⟧tp
⟦_,_⟧ {K = K} (new c) m = F.new c
⟦_,_⟧ {K = K} (var x) m =
  subst (λ a → ⟦ K ⟧ctx F.⊢ (F.var x) ∈ a) (⟦lookup-ctx⟧≡lookup-⟦ctx⟧ K x) (F.var x)
⟦_,_⟧ {K = K} {a = ∀' a} (Λ wt-e) m =
  F.Λ (
    subst
      (λ c → c F.⊢ ⟦ wt-e , #tvar m ⟧t ∈ ⟦ a ⟧tp)
      (⟦ctx-weaken⟧≡ctx-weaken K)
      ⟦ wt-e , (#tvar m) ⟧)
⟦ λ' a wt-e , m ⟧ = F.λ' ⟦ a ⟧tp ⟦ wt-e , #var a m ⟧
⟦_,_⟧ {K = K} (_[_] {a = a} wt-tc b) m =
  subst
    (λ c → ⟦ K ⟧ctx F.⊢ ⟦ wt-tc [ b ] , m ⟧t ∈ c)
    (sym $ ⟦sub⟧≡sub a b)
    (⟦ wt-tc , m ⟧ F.[ ⟦ b ⟧tp ])
⟦ (wt-f · wt-e) , m ⟧ = ⟦ wt-f , m ⟧ F.· ⟦ wt-e , m ⟧
⟦ (ρ {a = a} unamb-a wt-e) , m ⟧ = F.λ' ⟦ a ⟧tp ⟦ wt-e , (#ivar a m) ⟧
⟦ (wt-r ⟨ e ⟩) , m ⟧ = ⟦ wt-r , m ⟧ F.· ⟦ e , m ⟧
⟦ (¿ a K⊢ᵣa) , m ⟧ = proj₂ ⟦ K⊢ᵣa , m ⟧r
⟦ (let'_in'_ {a = a} wt-e₁ wt-e₂) , m ⟧ = (F.λ' ⟦ a ⟧tp ⟦ wt-e₂ , (#var a m) ⟧) F.· ⟦ wt-e₁ , m ⟧
⟦ (implicit_in'_ {a = a} wt-e₁ wt-e₂) , m ⟧ =
  (F.λ' ⟦ a ⟧tp ⟦ wt-e₂ , (#ivar a m) ⟧) F.· ⟦ wt-e₁ , m ⟧ 
