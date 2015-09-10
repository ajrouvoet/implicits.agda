open import Prelude hiding (id; _>>=_)

module Implicits.Oliveira.Types.Unification (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Implicits.Oliveira.Types TC _tc≟_
open import Data.Vec.Properties
open import Data.Nat.Properties.Simple
open import Category.Monad

open import Data.Maybe using (monad; functor)
open import Level using () renaming (zero to level₀)
open RawMonad {level₀} monad using (_>>=_; return)
open import Category.Functor
open RawFunctor {level₀} functor
open import Data.Star hiding (_>>=_)

open import Implicits.Oliveira.Substitutions TC _tc≟_
open import Implicits.Oliveira.Substitutions.Lemmas TC _tc≟_

module McBride where

  thin : ∀ {n} → Fin (suc n) → Fin n → Fin (suc n)
  thin zero y = suc y
  thin (suc x) zero = zero
  thin (suc x) (suc y) = suc (thin x y)

  thick : ∀ {n} → (x y : Fin (suc n)) → Maybe (Fin n)
  thick zero zero = nothing
  thick zero (suc y) = just y
  thick {zero} (suc ()) zero
  thick {suc n} (suc x) zero = just zero
  thick {zero} (suc ()) _ 
  thick {suc n} (suc x) (suc y) = suc <$> (thick x y)

  check : ∀ {n} → Fin (suc n) → Type (suc n) → Maybe (Type n)
  check n (simpl (tvar m)) = (simpl ∘ tvar) <$> (thick n m)
  check n (simpl (tc x)) = just (simpl (tc x))
  check n (simpl (a →' b)) with check n a | check n b
  check n (simpl (a →' b)) | just x | just y = just (simpl (x →' y))
  check n (simpl (a →' b)) | _ | nothing = nothing
  check n (simpl (a →' b)) | nothing | _ = nothing
  check n (a ⇒ b) with check n a | check n b
  check n (a ⇒ b) | just x | just y = just (simpl (x →' y))
  check n (a ⇒ b) | _ | nothing = nothing
  check n (a ⇒ b) | nothing | _ = nothing
  check n (∀' t) with check (suc n) t
  check n (∀' t) | just x = just (∀' x)
  check n (∀' t) | nothing = nothing

  substitute : {m n : ℕ} → (Fin m → Type n) → Type m → Type n
  substitute f (simpl (tc x)) = simpl (tc x)
  substitute f (simpl (tvar n)) = f n
  substitute f (simpl (a →' b)) = simpl (substitute f a →' substitute f b)
  substitute f (a ⇒ b) = substitute f a ⇒ substitute f b
  substitute f (∀' a) =
    ∀' (substitute (λ{
      zero    → simpl (tvar zero);
      (suc x) → tp-weaken $ f x }
    ) a)

  _for_ : ∀ {n} → Type n → Fin (suc n) → Fin (suc n) → Type n
  _for_ t' x y with thick x y
  _for_ t' x y | just y' = simpl $ tvar y'
  _for_ t' x y | nothing = t'

  data ASub : ℕ → ℕ → Set where
    _//_ : ∀ {ν} → (t' : Type ν) → Fin (suc ν) → ASub (suc ν) ν

  AList : ℕ → ℕ → Set
  AList m n = Star ASub m n

  asub-weaken : ∀ {m n} → ASub m n → ASub (suc m) (suc n)
  asub-weaken (t' // x) = tp-weaken t' // (inject₁ x)

  asub-weaken⋆ : ∀ {m n} α → ASub m n → ASub (m N+ α) (n N+ α)
  asub-weaken⋆ {m} {n} zero x = subst₂ (λ u v → ASub u v)
                                       (sym $ +-right-identity m) (sym $ +-right-identity n) x 
  asub-weaken⋆ {m} {n} (suc α) x = subst₂ (λ u v → ASub u v)
                                          (sym $ +-suc m α) (sym $ +-suc n α) (asub-weaken⋆ α (asub-weaken x))

  alist-weaken : ∀ {m n} → AList m n → AList (suc m) (suc n)
  alist-weaken s = gmap suc (λ x → asub-weaken x) s

  alist-weaken⋆ : ∀ {m n} α → AList m n → AList (m N+ α) (n N+ α)
  alist-weaken⋆ α s = gmap (λ n → n N+ α) (asub-weaken⋆ α) s

  _◇_ : ∀ {l m n} → (Fin m → Type n) → (Fin l → Type m) → (Fin l → Type n)
  f ◇ g = substitute f ∘ g

  asub : ∀ {m n} → (σ : AList m n) → Fin m → Type n
  asub ε = simpl ∘ tvar
  asub (t' // x ◅ y) =  asub y ◇ (t' for x)

  flex-flex : ∀ {m} → (x y : Fin m) → ∃ (AList m)
  flex-flex {zero} () y
  flex-flex {suc m} x y with thick x y
  flex-flex {suc m} x y | just z = m , simpl (tvar z) // x ◅ ε
  flex-flex {suc m} x y | nothing = (suc m) , ε

  flex-rigid : ∀ {m} → Fin m → Type m → Maybe (∃ (AList m))
  flex-rigid {zero} () t
  flex-rigid {suc m} x t with check x t
  flex-rigid {suc m} x t | just y = just (m , y // x ◅ ε)
  flex-rigid {suc m} x t | nothing = nothing

  mgu : ∀ {ν} (s t : Type ν) → Maybe (∃ (AList ν))
  mgu {ν} s t = amgu s t (ν , ε)
    where
      postulate amgu : ∀ {ν} (s t : Type ν) → ∃ (AList ν) → Maybe (∃ (AList ν))
      {-
      -- non-matching constructors
      amgu (simpl (tc x)) (simpl (a →' b)) acc = nothing
      amgu (simpl (a →' b)) (simpl (tc x)) acc = nothing
      amgu (_ ⇒ _) (simpl (tc _)) acc = nothing
      amgu (simpl (tc _)) (_ ⇒ _) acc = nothing
      amgu (_ ⇒ _) (simpl (_ →' _)) acc = nothing
      amgu (simpl (a →' b)) (t₁ ⇒ t₂) acc = nothing
      amgu (_ ⇒ _) (∀' _) x = nothing
      amgu (∀' _) (_ ⇒ _) x = nothing
      amgu (simpl (_ →' _)) (∀' _) x = nothing
      amgu (∀' _) (simpl (_ →' _)) x = nothing
      amgu (∀' _) (simpl (tc _)) x = nothing
      amgu (simpl (tc _)) (∀' _) x = nothing

      -- matching
      amgu (simpl (tc x)) (simpl (tc y)) acc = just acc
      amgu (simpl (a →' b)) (simpl (a' →' b')) acc = amgu b b' acc >>= amgu a a'
      amgu (a ⇒ b) (a' ⇒ b') acc = _>>=_ (amgu b b' acc) (amgu a a')
      amgu (∀' a) (∀' b) acc = {!!}

      -- var-var
      amgu (simpl (tvar x)) (simpl (tvar y)) (m , ε) = just (flex-flex x y)

      -- var-rigid / rigid-var
      amgu t (simpl (tvar x)) (m , ε) = flex-rigid x t 
      amgu (simpl (tvar x)) t  (m , ε) = flex-rigid x t 

      amgu s t (m , t' // x ◅ us) with amgu (substitute σ s) (substitute σ t) (m , us)
        where σ = (t' for x )
      amgu s t (m , t' // x ◅ us) | just (m' , us') = just (m' , t' // x ◅ us')
      amgu s t (m , t' // x ◅ us) | nothing = nothing
      -}

  {-
  MGU : ∀ {ν} → (α : Fin (suc ν)) → (a b : Type ν) → Set
  MGU {ν} α a b = ∃ λ (s : AList (toℕ α) zero) →
    (substitute (asub $ alist-weaken⋆ (proj₁ eq) s)) (subst Type (proj₂ eq) a) ≡ b
    where
      lem : ∀ y (x : Fin (suc y)) → ∃ λ a → y ≡ (toℕ x) N+ a
      lem zero zero = zero , refl
      lem zero (suc ())
      lem (suc x) zero = suc x , refl
      lem (suc x) (suc y) = , cong suc (proj₂ $ lem x y)
      eq = lem ν α
      -}

open import Data.Fin.Substitution
open TypeSubst hiding (subst)

mutual 

  MGU : ∀ {ν} → (α : Fin (suc ν)) → (a b : Type ν) → Set 
  MGU {ν} α a b = ∃ λ (s : Sub Type (toℕ α) ν) → a / (embed α s) ≡ b

  apply-unifier : ∀ {ν} α {a b : Type ν} → MGU α a b → Type ν → Type ν
  apply-unifier α u a = a / (embed α (proj₁ u))

  -- subn : ∀ {n} → Fin (suc n) → Type n → Sub Type (suc n) n
  -- subn {n} x a = id {n} [ x ]≔ a

  postulate mgu-id : ∀ {ν} {α} a → MGU {ν} α a a

  -- TODO : every substitution should remove a type variable
  postulate mgu : ∀ {ν} → (α : Fin (suc ν)) → (a b : Type ν) → Maybe (MGU α a b)

  postulate mgu-sound : ∀ {ν} {α} {a b : Type ν} → mgu α a b ≡ nothing → ¬ MGU α a b

  mgu-unifies : ∀ {ν} {α : Fin (suc ν)} {a b} (u : (MGU α a b)) → apply-unifier α u a ≡ b
  mgu-unifies u = proj₂ u

  {-
  mgu (simpl (tc x)) (simpl (tc y)) with x tc≟ y
  mgu (simpl (tc x)) (simpl (tc .x)) | yes refl = yes (id , TypeLemmas.id-vanishes (simpl $ tc x))
  mgu (simpl (tc x)) (simpl (tc y))  | no x≢y = no (λ{ (s , tc-x/s≡y) → x≢y (helper s tc-x/s≡y) }) 
    where
        helper : ∀ {c d n m} (s : Sub Type n m) → (simpl (tc c)) / s ≡ (simpl (tc d)) → c ≡ d
        helper _ refl = refl
  mgu (simpl (tvar n)) x = yes (id [ n ]≔ x , lookup∘update n id x)
  mgu (simpl (a →' b)) (simpl (a' →' b')) with mgu a a' 
  mgu (simpl (a →' b)) (simpl (a' →' b')) | no ¬p = no (λ{ (s , p) → ¬p (s , helper a b a' b' s p) })
    where
        helper : ∀ {n m} a b a' b' (σ : Sub Type n m) →
                 (simpl $ a →' b) / σ ≡ (simpl $ a' →' b') → a / σ ≡ a'
        helper _ _ _ _ _ refl = refl
  mgu (simpl (a →' b)) (simpl (a' →' b')) | yes (s , p) with mgu b (b' / s)
  mgu (simpl (a →' b)) (simpl (a' →' b')) | yes (s , p) | yes (s' , p') = yes (s ⊙ s' , helper)
    where
      helper : (simpl (a →' b)) / (s ⊙ s') ≡ (simpl (a' →' b'))
      helper = begin
        (simpl (a →' b)) / (s ⊙ s')
          ≡⟨ refl ⟩
        simpl ((a / (s ⊙ s')) →' (b / (s ⊙ s')))
          ≡⟨ ? ⟩
        simpl ((a / s / s') →' (b / (s ⊙ s')))
          ≡⟨ ? ⟩
        (simpl (a' →' b')) ∎
  mgu (simpl (a →' b)) (simpl (a' →' b')) | yes (s , p) | no ¬p' = {!!}
  mgu (a ⇒ b) (a' ⇒ b') = {!!}
  mgu (∀' a) (∀' b) with mgu a b
  mgu (∀' a) (∀' b) | yes ( s ∷ ss , p) with s ≟ (simpl (tvar zero))
  mgu (∀' a) (∀' b) | yes ( s ∷ ss , p) | yes s≡zero = yes {!ss , ?!}
  mgu (∀' a) (∀' b) | yes ( s ∷ ss , p) | no s≢zero = {!s!}
  mgu (∀' a) (∀' b) | no ¬p = {!!}

  -- obviously "no"
  mgu (simpl (tc x)) (simpl (tvar n)) = no (λ{ (s  , ()) })
  mgu (simpl (x →' x₁)) (simpl (tvar n)) =  no (λ{ (s  , ()) })
  mgu (a ⇒ b) (simpl (tvar n)) = no (λ { (s , ()) })
  mgu (∀' x) (simpl (tvar n)) = no (λ{ (s  , ()) })
  mgu (simpl (tc x)) (simpl (x₁ →' x₂)) = no (λ { (s , ()) })
  mgu (simpl (x →' x₁)) (simpl (tc x₂)) = no (λ { (s , ()) })
  mgu (simpl a) (b ⇒ b₁) = no (λ { (s , ()) })
  mgu (simpl a) (∀' b) = no (λ { (s , ()) })
  mgu (a ⇒ a₁) (simpl x) = no (λ { (s , ()) })
  mgu (a ⇒ a₁) (∀' b) = no (λ { (s , ()) })
  mgu (∀' a) (simpl x) = no (λ { (s , ()) })
  mgu (∀' a) (b ⇒ b₁) = no (λ { (s , ()) })
  -}

  {-
  data MGU {ν} : (a b : Type ν) → Set where
    uinst : ∀ n r → MGU r (simpl $ tvar n)
    uvar : ∀ n → MGU (simpl $ tvar n) (simpl $ tvar n)
    ufun : ∀ {a b a' b'} → (u₁ : MGU a a') → MGU b (apply-mgu u₁ b') →
           MGU (simpl (a →' b)) (simpl (a' →' b'))
    urul : ∀ {a b a' b'} → (u₁ : MGU a a') → MGU b (apply-mgu u₁ b') → MGU (a ⇒ b) (a' ⇒ b')
    uabs : ∀ {a b} → MGU a b → MGU (∀' a) (∀' b)

  apply-mgu : ∀ {ν} {a b : Type ν} → MGU a b → Type ν → Type ν
  apply-mgu (uinst n r) a = a TypeSubst./ (id [ n ]≔ r)
  apply-mgu (uvar n) a = a
  apply-mgu (ufun u v) a = apply-mgu v $ apply-mgu u a
  apply-mgu (urul u v) a = apply-mgu v $ apply-mgu u a
  apply-mgu (uabs u) a = {!!}
  -}

  -- postulate unifier-unifies : ∀ {ν} {a b : Type ν} → (u : MGU a b) → apply-mgu u a ≡ b

-- mgu : ∀ {ν} → (a b : Type ν) → 
