module Implicits.Calculus.Denotational where

open import Prelude

open import Implicits.Calculus.WellTyped
open import Implicits.SystemF.WellTyped as F using ()

⟦_⟧tp : ∀ {ν} → Type ν → F.Type ν
⟦ tvar n ⟧tp = F.tvar n
⟦ a →' b ⟧tp = ⟦ a ⟧tp F.→' ⟦ b ⟧tp
⟦ ∀' x ⟧tp = F.∀' ⟦ x ⟧tp
⟦ a ⇒ b ⟧tp = ⟦ a ⟧tp F.→' ⟦ b ⟧tp

⟦_⟧ctx : ∀ {ν n} → Ktx ν n → F.Ctx ν n
⟦ Γ , Δ ⟧ctx = map ⟦_⟧tp Γ

-- construct an System F term from an implicit resolution
postulate ⟦_⟧i : ∀ {ν n} {K : Ktx ν n} {a}  → K Δ↝ a → F.Term ν n
postulate ⟦⟧i-wt-lemma : ∀ {ν n} {K : Ktx ν n} {a} (i : K Δ↝ a) → ⟦ K ⟧ctx F.⊢ ⟦ i ⟧i ∈ ⟦ a ⟧tp

⟦_⟧ : ∀ {ν n} {K : Ktx ν n} {t a} → K ⊢ t ∈ a → F.Term ν n
⟦_⟧ (var x) = F.var x
⟦_⟧ (Λ t) = F.Λ ⟦ t ⟧
⟦_⟧ (λ' a x) = F.λ' ⟦ a ⟧tp ⟦ x ⟧
⟦_⟧ (f [ b ]) = F._[_] ⟦ f ⟧ ⟦ b ⟧tp
⟦_⟧ (f · e) = ⟦ f ⟧ F.· ⟦ e ⟧
⟦_⟧ (ρ a x) = F.λ' ⟦ a ⟧tp ⟦ x ⟧
⟦_⟧ (_⟨⟩ f e∈Δ) = ⟦ f ⟧ F.· ⟦ e∈Δ ⟧i
⟦_⟧ (implicit_in'_ {a = a} t e) = (F.λ' ⟦ a ⟧tp ⟦ e ⟧) F.· ⟦ t ⟧

lookup⋆⟦⟧ctx : ∀ {ν n} (K : Ktx ν n) x → lookup x ⟦ K ⟧ctx ≡ ⟦ lookup x $ proj₁ K ⟧tp
lookup⋆⟦⟧ctx K x = sym $ lookup⋆map (proj₁ K) ⟦_⟧tp x

postulate weaken-tp⋆⟦⟧tp : ∀ {ν} (tp : Type ν) → ⟦ tp TypeSubst./ TypeSubst.wk ⟧tp ≡ ⟦ tp ⟧tp F.TypeSubst./ F.TypeSubst.wk

ctx-weaken⋆⟦⟧ctx : ∀ {ν n} (K : Ktx ν n) → ⟦ ktx-weaken K ⟧ctx ≡ F.ctx-weaken ⟦ K ⟧ctx
ctx-weaken⋆⟦⟧ctx ([] , Δ) = refl
ctx-weaken⋆⟦⟧ctx (x ∷ Γ , Δ) with ctx-weaken⋆⟦⟧ctx (Γ , Δ)
ctx-weaken⋆⟦⟧ctx (x ∷ Γ , Δ) | ih = begin
  ⟦ ktx-weaken (x ∷ Γ , Δ) ⟧ctx ≡⟨ refl ⟩ 
  ⟦ x TypeSubst./ TypeSubst.wk ⟧tp ∷ xs ≡⟨ eq1 x ⟩ 
  ⟦ x ⟧tp F.TypeSubst./ F.TypeSubst.wk ∷ ⟦ ktx-weaken (Γ , Δ) ⟧ctx ≡⟨ eq2 ⟩
  ⟦ x ⟧tp F.TypeSubst./ F.TypeSubst.wk ∷ F.ctx-weaken ⟦ Γ , Δ ⟧ctx ≡⟨ refl ⟩
  F.ctx-weaken ⟦ x ∷ Γ , Δ ⟧ctx ∎
  where
    xs = (map ⟦_⟧tp $ map (λ s → s TypeSubst./ TypeSubst.wk) Γ)
    eq1 = λ x → cong (flip _∷_ xs) (weaken-tp⋆⟦⟧tp x)
    eq2 = cong (_∷_ (⟦ x ⟧tp F.TypeSubst./ F.TypeSubst.wk)) ih

postulate tp/tp⋆⟦⟧ctx : ∀ {ν} (a : Type (suc ν)) b → ⟦ a tp[/tp b ] ⟧tp ≡ ⟦ a ⟧tp F.tp[/tp ⟦ b ⟧tp ]

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
