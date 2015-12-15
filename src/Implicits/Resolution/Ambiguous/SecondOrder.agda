open import Prelude
open import Function.Equivalence using (_⇔_; equivalence)
open import Data.Fin.Substitution
open import Data.List.Properties
open import Relation.Binary.HeterogeneousEquality as H using ()
module HR = H.≅-Reasoning
open import Data.Vec.Properties as VP using ()

module Implicits.Resolution.Ambiguous.SecondOrder TC _tc≟_ where

open import Implicits.Syntax TC _tc≟_
open import Implicits.Resolution.Ambiguous.Resolution TC _tc≟_
open import Implicits.Substitutions TC _tc≟_
open import Implicits.Substitutions.Lemmas TC _tc≟_
open TypeSubst hiding (subst)
module TS = TypeSubst

open import SystemF TC as F using ()

private
  ⟦_⟧tp← : ∀ {ν} → F.Type ν → Type ν
  ⟦ F.tc x ⟧tp← = simpl (tc x)
  ⟦ F.tvar n ⟧tp← = simpl (tvar n)
  ⟦ a F.→' b ⟧tp← = (⟦ a ⟧tp← ⇒ ⟦ b ⟧tp←)
  ⟦ a F.⟶ b ⟧tp← = simpl (⟦ a ⟧tp← →' ⟦ b ⟧tp←)
  ⟦ F.∀' x ⟧tp← = ∀' ⟦ x ⟧tp←

  ⟦_⟧tp→ : ∀ {ν} → Type ν → F.Type ν
  ⟦ simpl (tc x) ⟧tp→ = F.tc x
  ⟦ simpl (tvar n) ⟧tp→ = F.tvar n
  ⟦ simpl (a →' b) ⟧tp→ = ⟦ a ⟧tp→ F.⟶ ⟦ b ⟧tp→
  ⟦ a ⇒ b ⟧tp→ = ⟦ a ⟧tp→ F.→' ⟦ b ⟧tp→
  ⟦ ∀' x ⟧tp→ = F.∀' ⟦ x ⟧tp→

  ⟦_⟧tps→ : ∀ {ν n} → Vec (Type ν) n → Vec (F.Type ν) n
  ⟦ v ⟧tps→ = map (⟦_⟧tp→) v

  ⟦_⟧ctx← : ∀ {ν n} → Vec (F.Type ν) n → List (Type ν)
  ⟦ v ⟧ctx← = toList $ map ⟦_⟧tp← v

  ⟦_⟧ctx→ : ∀ {ν} → (Δ : ICtx ν) → Vec (F.Type ν) (List.length (List.map ⟦_⟧tp→ Δ))
  ⟦ Δ ⟧ctx→ = fromList (List.map ⟦_⟧tp→ Δ)

  ⟦_⟧term→ : ∀ {ν} {Δ : ICtx ν} {r} → Δ ⊢ᵣ r → F.Term ν (List.length Δ)
  ⟦_⟧term→ {ν} {Δ} (r-tabs x) = F.Λ p
    where
      p : F.Term (suc ν) (List.length Δ)
      p = subst (λ u → F.Term (suc ν) u) (length-map _ Δ) ⟦ x ⟧term→
  ⟦ r-tapp a x ⟧term→ = ⟦ x ⟧term→ F.[ ⟦ a ⟧tp→ ]
  ⟦ r-ivar x ⟧term→ = F.var (index x)
    where open import Data.List.Any
  ⟦ r-iabs {a = a} x ⟧term→ = F.λ' ⟦ a ⟧tp→ ⟦ x ⟧term→
  ⟦ r-iapp f e ⟧term→ = ⟦ f ⟧term→ F.· ⟦ e ⟧term→

  
  ⟦a/var⟧tp→ : ∀ {ν ν'} (a : Type ν) (s : Vec (Fin ν') ν) → ⟦ a /Var s ⟧tp→ ≡ ⟦ a ⟧tp→ F./Var s
  ⟦a/var⟧tp→ (simpl (tc x)) s = refl
  ⟦a/var⟧tp→ (simpl (tvar n)) s = refl
  ⟦a/var⟧tp→ (simpl (a →' b)) s = cong₂ F._⟶_ (⟦a/var⟧tp→ a s) (⟦a/var⟧tp→ b s)
  ⟦a/var⟧tp→ (a ⇒ b) s = cong₂ F._→'_ (⟦a/var⟧tp→ a s) (⟦a/var⟧tp→ b s)
  ⟦a/var⟧tp→ (∀' a) s = cong F.∀' (⟦a/var⟧tp→ a (s VarSubst.↑))
  
  ⟦weaken⟧ : ∀ {ν} (a : Type ν) → ⟦ weaken a ⟧tp→ ≡ F.weaken ⟦ a ⟧tp→
  ⟦weaken⟧ x = ⟦a/var⟧tp→ x VarSubst.wk

  -- helper lemma on mapping type-semantics over weakend substitutions
  ⟦⟧tps→⋆weaken : ∀ {ν n} (xs : Vec (Type ν) n) →
                 ⟦ (map TS.weaken xs) ⟧tps→ ≡ (map F.weaken ⟦ xs ⟧tps→)
  ⟦⟧tps→⋆weaken xs = begin
    (map ⟦_⟧tp→ ∘ map TS.weaken) xs
      ≡⟨ sym $ (VP.map-∘ ⟦_⟧tp→ TS.weaken) xs ⟩
    map (⟦_⟧tp→ ∘ TS.weaken) xs
      ≡⟨ (VP.map-cong ⟦weaken⟧) xs ⟩
    map (F.weaken ∘ ⟦_⟧tp→) xs
      ≡⟨ (VP.map-∘ F.weaken ⟦_⟧tp→) xs ⟩ 
    map F.weaken (map ⟦_⟧tp→ xs) ∎

  -- the semantics of identity type-substitution is exactly 
  -- system-f's identity type substitution
  ⟦id⟧tp→ : ∀ {n} → map ⟦_⟧tp→ (TS.id {n}) ≡ F.id
  ⟦id⟧tp→ {zero} = refl
  ⟦id⟧tp→ {suc n} = begin
    map ⟦_⟧tp→ (simpl (tvar zero) ∷ map TS.weaken (TS.id {n})) 
      ≡⟨ refl ⟩
    F.tvar zero ∷ (map ⟦_⟧tp→ (map TS.weaken (TS.id {n}))) 
      ≡⟨ cong (_∷_ (F.tvar zero)) (⟦⟧tps→⋆weaken (TS.id {n})) ⟩
    F.tvar zero ∷ (map F.weaken (map ⟦_⟧tp→ (TS.id {n}))) 
      ≡⟨ cong (λ e → F.tvar zero ∷ (map F.weaken e)) ⟦id⟧tp→ ⟩
    F.tvar zero ∷ (map F.weaken (F.id {n})) 
      ≡⟨ refl ⟩
    F.id ∎

  -- the semantics of type weakening is exactly system-f's type weakening
  ⟦wk⟧tp→ : ∀ {n} → map ⟦_⟧tp→ (TS.wk {n}) ≡ F.wk {n}
  ⟦wk⟧tp→ = begin
    map ⟦_⟧tp→ TS.wk 
      ≡⟨ ⟦⟧tps→⋆weaken TS.id ⟩
    map F.weaken (map ⟦_⟧tp→ TS.id) 
      ≡⟨ cong (map F.weaken) ⟦id⟧tp→ ⟩
    F.wk ∎

  ⟦⟧tps→⋆↑ :  ∀ {ν n} (v : Vec (Type ν) n) → ⟦ v TS.↑ ⟧tps→ ≡ ⟦ v ⟧tps→ F.↑
  
  -- lookup in and interpreted context Γ is equivalent to interpreting a type, looked up in K
  -- lookup⋆⟦⟧ctx : ∀ {ν n} (K : Ktx ν n) x → lookup x ⟦ K ⟧ctx ≡ ⟦ lookup x $ proj₁ K ⟧tp→
  -- lookup⋆⟦⟧ctx K x = sym $ lookup⋆map (proj₁ K) ⟦_⟧tp→ x
  
  -- type substitution commutes with interpreting types
  /⋆⟦⟧tp→ : ∀ {ν μ} (tp : Type ν) (σ : Sub Type ν μ) → ⟦ tp TS./ σ ⟧tp→ ≡ ⟦ tp ⟧tp→ F./ (map ⟦_⟧tp→ σ)
  /⋆⟦⟧tp→ (simpl (tc c)) σ = refl
  /⋆⟦⟧tp→ (simpl (tvar n)) σ = begin
    ⟦ lookup n σ ⟧tp→ 
      ≡⟨ lookup⋆map σ ⟦_⟧tp→ n ⟩
    ⟦ simpl (tvar n) ⟧tp→ F./ (map ⟦_⟧tp→ σ) ∎
  /⋆⟦⟧tp→ (l ⇒ r) σ = cong₂ F._→'_ (/⋆⟦⟧tp→ l σ) (/⋆⟦⟧tp→ r σ)
  /⋆⟦⟧tp→ (simpl (l →' r)) σ = cong₂ F._⟶_ (/⋆⟦⟧tp→ l σ) (/⋆⟦⟧tp→ r σ)
  /⋆⟦⟧tp→ (∀' a) σ = begin
    F.∀' ⟦ (a TS./ σ TS.↑) ⟧tp→
      ≡⟨ cong F.∀' (/⋆⟦⟧tp→ a (σ TS.↑)) ⟩
    F.∀' (⟦ a ⟧tp→ F./ ⟦ σ TS.↑ ⟧tps→)
      ≡⟨ cong (λ u → F.∀' (⟦ a ⟧tp→ F./ u)) ((⟦⟧tps→⋆↑ σ)) ⟩
    ⟦ ∀' a ⟧tp→ F./ (map ⟦_⟧tp→ σ) ∎
  
  ⟦a/sub⟧tp→ : ∀ {ν} (a : Type (suc ν)) b → ⟦ a TS./ (TS.sub b) ⟧tp→ ≡ ⟦ a ⟧tp→ F./ (F.sub ⟦ b ⟧tp→)
  ⟦a/sub⟧tp→ a b = begin
    ⟦ a TS./ (TS.sub b) ⟧tp→
    ≡⟨ /⋆⟦⟧tp→ a (b ∷ TS.id) ⟩
    (⟦ a ⟧tp→ F./ (map ⟦_⟧tp→ (b ∷ TS.id)) )
    ≡⟨ refl ⟩
    (⟦ a ⟧tp→ F./ (⟦ b ⟧tp→ ∷ (map ⟦_⟧tp→ TS.id)) )
    ≡⟨ cong (λ s → ⟦ a ⟧tp→ F./ (⟦ b ⟧tp→ ∷ s)) ⟦id⟧tp→ ⟩
    (⟦ a ⟧tp→ F./ (F.sub ⟦ b ⟧tp→)) ∎

  -- interpretation of contexts 
  ⟦⟧tps→⋆↑ xs = begin
    F.tvar zero ∷ (map ⟦_⟧tp→ (map TS.weaken xs)) 
      ≡⟨ cong (_∷_ (F.tvar zero)) (⟦⟧tps→⋆weaken xs) ⟩
    F.tvar zero ∷ (map F.weaken (map ⟦_⟧tp→ xs)) 
      ≡⟨ refl ⟩
    (map ⟦_⟧tp→ xs) F.↑ ∎
  
  ⟦a/wk⟧tp→ : ∀ {ν} → (a : Type ν) → ⟦ a / wk ⟧tp→ ≡ ⟦ a ⟧tp→ F./ F.wk
  ⟦a/wk⟧tp→ tp = begin
    ⟦ tp TS./ TS.wk ⟧tp→
      ≡⟨ /⋆⟦⟧tp→ tp TS.wk ⟩
    ⟦ tp ⟧tp→ F./ (map ⟦_⟧tp→ TS.wk) 
      ≡⟨ cong (λ e → ⟦ tp ⟧tp→ F./ e) ⟦wk⟧tp→ ⟩
    ⟦ tp ⟧tp→ F./ F.wk ∎

  ⟦a[/b]⟧tp← : ∀ {ν} (a : F.Type (suc ν)) b → ⟦ a F./ (F.sub b) ⟧tp← ≡ ⟦ a ⟧tp← / (sub ⟦ b ⟧tp←)
  ⟦a[/b]⟧tp← tp = {!!}

  ⟦weaken⟧ctx← : ∀ {ν n} {Γ : F.Ctx ν n} → ⟦ F.ctx-weaken Γ ⟧ctx← ≡ ictx-weaken ⟦ Γ ⟧ctx←
  ⟦weaken⟧ctx← = {!!}

  ∷cong : ∀ {ν n n'} {x : F.Type ν} {xs : F.Ctx ν n} {xs' : F.Ctx ν n'} → n ≡ n' → xs H.≅ xs' →
          x ∷ xs H.≅ x ∷ xs'
  ∷cong refl H.refl = H.refl
       
  length-weaken-Δ : ∀ {ν} (Δ : ICtx ν) → (List.length (List.map ⟦_⟧tp→ (ictx-weaken Δ))) ≡ (List.length (List.map ⟦_⟧tp→ Δ))
  length-weaken-Δ Δ = begin 
    (List.length (List.map ⟦_⟧tp→ (List.map (λ s → s / wk) Δ)))
      ≡⟨ cong List.length (sym $ map-compose Δ) ⟩
    (List.length (List.map (⟦_⟧tp→ ∘ (λ s → s / wk)) Δ))
      ≡⟨ length-map _ Δ ⟩
    List.length Δ
      ≡⟨ sym $ length-map _ Δ ⟩
    (List.length (List.map ⟦_⟧tp→ Δ)) ∎

  ⟦weaken⟧ctx→ : ∀ {ν} (Δ : ICtx ν) → F.ctx-weaken ⟦ Δ ⟧ctx→ H.≅ ⟦ ictx-weaken Δ ⟧ctx→
  ⟦weaken⟧ctx→ List.[] = H.refl
  ⟦weaken⟧ctx→ (x List.∷ xs) = HR.begin
    F.ctx-weaken ⟦ x List.∷ xs ⟧ctx→
      HR.≅⟨ H.refl ⟩
    (⟦ x ⟧tp→ F./ F.wk) ∷ F.ctx-weaken ⟦ xs ⟧ctx→
      HR.≅⟨ ∷cong (sym (length-weaken-Δ xs)) (⟦weaken⟧ctx→ xs) ⟩
    (⟦ x ⟧tp→ F./ F.wk) ∷ ⟦ ictx-weaken xs ⟧ctx→
      HR.≅⟨ H.cong (flip _∷_ ⟦ ictx-weaken xs ⟧ctx→) (H.≡-to-≅ $ sym $ ⟦a/wk⟧tp→ x) ⟩
    ⟦ x / wk ⟧tp→ ∷ ⟦ ictx-weaken xs ⟧ctx→
      HR.≅⟨ H.cong (λ u → ⟦ x / wk ⟧tp→ ∷ fromList u) (H.≡-to-≅ (sym (map-compose xs))) ⟩
    (fromList (List.map (⟦_⟧tp→ ∘ (λ s → s / wk)) (x List.∷ xs)))
      HR.≅⟨ H.cong fromList (H.≡-to-≅ (map-compose (x List.∷ xs))) ⟩
    ⟦ ictx-weaken (x List.∷ xs) ⟧ctx→ HR.∎

  from : ∀ {ν n t a} {Γ : F.Ctx ν n} → Γ F.⊢ t ∈ a → ⟦ Γ ⟧ctx← ⊢ᵣ ⟦ a ⟧tp←
  from (F.var x) = r-ivar (lem x _)
    where
      lem : ∀ {ν n} → (x : Fin n) → (v : F.Ctx ν n) → ⟦ lookup x v ⟧tp← List.∈ ⟦ v ⟧ctx←
      lem zero (x ∷ xs) = here refl
      lem (suc x) (v ∷ vs) = there (lem x vs) 
  from (F.Λ x) = r-tabs (subst (λ u → u ⊢ᵣ _) ⟦weaken⟧ctx← (from x))
  from (F.λ' {b = b} a x) = r-iabs (from x)
  from {Γ = Γ} (F._[_] {a = a} x b) = subst
    (λ u → ⟦ Γ ⟧ctx← ⊢ᵣ u)
    (sym (⟦a[/b]⟧tp← a b))
    (r-tapp ⟦ b ⟧tp← (from x))
  from (a F.· b) = r-iapp (from a) (from b)

  ⊢subst-n : ∀ {ν n n'} {Γ : F.Ctx ν n} {Γ' : F.Ctx ν n'} {t a} → (n-eq : n ≡ n') →
                       Γ H.≅ Γ' → Γ F.⊢ t ∈ a →
                       Γ' F.⊢ (subst (F.Term ν) n-eq t) ∈ a
  ⊢subst-n refl H.refl p = p

  postulate lookup⟦⟧ : ∀ {ν} (Δ : ICtx ν) {r} i → lookup i (fromList Δ) ≡ r →
                          (lookup (subst Fin (sym $ length-map _ Δ) i) ⟦ Δ ⟧ctx→) ≡ ⟦ r ⟧tp→

  to : ∀ {ν} {Δ : ICtx ν} {r} → (p : Δ ⊢ᵣ r) → ∃ λ t → ⟦ Δ ⟧ctx→ F.⊢ t ∈ ⟦ r ⟧tp→
  to {Δ = Δ} (r-tabs {r = r} p) with to p 
  to {Δ = Δ} (r-tabs {r = r} p) | _ , x =
    , F.Λ (⊢subst-n (length-weaken-Δ Δ) (H.sym $ ⟦weaken⟧ctx→ Δ) x)
  to (r-tapp a p) with to p
  to {Δ = Δ} (r-tapp {r = a} b p) | _ , x =
    , subst (λ u → ⟦ Δ ⟧ctx→ F.⊢ _ ∈ u) (sym $ ⟦a/sub⟧tp→ a b) (x F.[ ⟦ b ⟧tp→ ])
  to {Δ = Δ} (r-ivar x) =
    , let i , eq = ∈⟶index (List-∈⇒∈ x) in
        let i' = (subst Fin (sym $ length-map _ Δ) i) in
          subst (λ u → ⟦ Δ ⟧ctx→ F.⊢ (F.var i') ∈ u) (lookup⟦⟧ Δ i eq) (F.var i')
    where
      open import Data.List.Any
      open import Data.Vec.Properties
      open import Extensions.Vec
  to (r-iabs {a = a} p) = , F.λ' ⟦ a ⟧tp→ (proj₂ $ to p)
  to (r-iapp p p₁) = , (proj₂ $ to p) F.· (proj₂ $ to p₁)

-- iso : ∀ {ν} {Δ : ICtx ν} r → (p : Δ ⊢ᵣ r) ⇔ ⟦ Δ ⟧ctx→ F.⊢ ⟦ p ⟧term→ ∈ ⟦ r ⟧tp→
-- iso = equivalence {!!} {!!}
