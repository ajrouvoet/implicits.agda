open import Prelude hiding (id; _>>=_)

module Implicits.Oliveira.Types.Unification (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Implicits.Oliveira.Types TC _tc≟_
open import Data.Vec.Properties
open import Data.Nat as N using ()
open import Data.Nat.Properties.Simple
open import Category.Monad

open import Data.Maybe using (monad; functor)
open import Level using () renaming (zero to level₀)
open RawMonad {level₀} monad using (_>>=_; return)
open import Category.Functor
open RawFunctor {level₀} functor
open import Data.Star hiding (_>>=_)

open import Data.Fin.Substitution
open import Implicits.Oliveira.Substitutions TC _tc≟_
open import Implicits.Oliveira.Types.Unification.Types TC _tc≟_
open import Implicits.Oliveira.Substitutions.Lemmas TC _tc≟_

module McBride where

  private
    module M = MetaTypeMetaSubst
    module T = MetaTypeTypeSubst

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

  check : ∀ {ν n} → Fin (suc n) → MetaType (suc n) ν → Maybe (MetaType n ν)
  check n (tvar m) = just (tvar m)
  check n (mvar m) = mvar <$> (thick n m)
  check n (tc x) = just (tc x)
  check n (fork c a b) with check n a | check n b
  check n (fork c a b) | just x | just y = just (fork c x y)
  check n (fork c a b) | _ | nothing = nothing
  check n (fork c a b) | nothing | _ = nothing
  check n (∀' t) with check n t
  check n (∀' t) | just x = just (∀' x)
  check n (∀' t) | nothing = nothing

  check' : ∀ {ν n} → Fin (suc ν) → MetaType n (suc ν) → Maybe (MetaType n ν)
  check' n (tvar m) = tvar <$> (thick n m)
  check' n (mvar m) = just (mvar m)
  check' n (tc x) = just (tc x)
  check' n (fork c a b) with check' n a | check' n b
  check' n (fork c a b) | just x | just y = just (fork c x y)
  check' n (fork c a b) | _ | nothing = nothing
  check' n (fork c a b) | nothing | _ = nothing
  check' n (∀' t) with check' (suc n) t
  check' n (∀' t) | just x = just (∀' x)
  check' n (∀' t) | nothing = nothing

  substitute : {ν m n : ℕ} → (Fin m → MetaType n ν) → MetaType m ν → MetaType n ν
  substitute f (tc x) = tc x
  substitute f (tvar n) = tvar n
  substitute f (mvar n) = f n
  substitute f (fork c a b) = fork c (substitute f a) (substitute f b)
  substitute f (∀' a) = ∀' (substitute (λ{ x → T.weaken $ f x }) a)

  _for_ : ∀ {n ν} → MetaType n ν → Fin (suc n) → Fin (suc n) → MetaType n ν
  _for_ t' x y with thick x y
  _for_ t' x y | just y' = mvar y'
  _for_ t' x y | nothing = t'

  data ASub (ν : ℕ) : ℕ → ℕ → Set where
    _//_ : ∀ {m} → (t' : MetaType m ν) → Fin (suc m) → ASub ν (suc m) m

  AList : ℕ → ℕ → ℕ → Set
  AList ν m n = Star (ASub ν) m n

  asub-weaken : ∀ {ν m n} → ASub ν m n → ASub (suc ν) m n
  asub-weaken (t' // x) = T.weaken t' // x

  alist-weaken : ∀ {ν m n} → AList ν m n → AList (suc ν) m n
  alist-weaken s = gmap Prelude.id (λ x → asub-weaken x) s

  _◇_ : ∀ {l m n ν} → (Fin m → MetaType n ν) → (Fin l → MetaType m ν) → (Fin l → MetaType n ν)
  f ◇ g = substitute f ∘ g

  asub : ∀ {ν m n} → (σ : AList ν m n) → Fin m → MetaType n ν
  asub ε = mvar
  asub (t' // x ◅ y) =  asub y ◇ (t' for x)

  flex-flex : ∀ {m ν} → (x y : Fin m) → ∃ (AList ν m)
  flex-flex {zero} () y
  flex-flex {suc m} x y with thick x y
  flex-flex {suc m} x y | just z = m , (mvar z) // x ◅ ε
  flex-flex {suc m} x y | nothing = (suc m) , ε

  flex-rigid : ∀ {m ν} → Fin m → MetaType m ν → Maybe (∃ (AList ν m))
  flex-rigid {zero} () t
  flex-rigid {suc m} x t with check x t
  flex-rigid {suc m} x t | just y = just (m , y // x ◅ ε)
  flex-rigid {suc m} x t | nothing = nothing

  mgu : ∀ {m ν} (s t : MetaType m ν) → Maybe (∃ (AList ν m))
  mgu {ν} s t = amgu s t (ν , ε)
    where
      amgu : ∀ {ν m} (s t : MetaType m ν) → ∃ (AList ν m) → Maybe (∃ (AList ν m))
      -- non-matching constructors
      amgu (tc x) (fork _ _ _) acc = nothing
      amgu (tc _) (∀' _) x = nothing
      amgu (tc _) (tvar _) x = nothing
      amgu (tc _) (mvar _) acc = nothing
      amgu (fork _ _ _) (tc _) acc = nothing
      amgu (fork _ _ _) (∀' _) x = nothing
      amgu (fork _ _ _) (tvar _) x = nothing
      amgu (fork _ _ _) (mvar _) acc = nothing
      amgu (∀' _) (fork _ _ _) x = nothing
      amgu (∀' _) (tc _) x = nothing
      amgu (∀' _) (tvar _) x = nothing
      amgu (∀' _) (mvar _) acc = nothing
      amgu (tvar _) (fork _ _ _) x = nothing
      amgu (tvar _) (∀' _) x = nothing
      amgu (tvar _) (tc _) x = nothing
      amgu (tvar _) (mvar _) acc = nothing

      -- matching constructors
      amgu (fork c _ _) (fork d _ _) acc with c fork≟ d
      amgu (fork c a b) (fork d a' b') acc | yes p = _>>=_ (amgu b b' acc) (amgu a a')
      amgu (fork c x x₁) (fork d x₂ x₃) acc | no ¬p = nothing 
      amgu (tc x) (tc y) acc with x tc≟ y 
      amgu (tc x) (tc y) acc | yes p = just (, ε)
      amgu (tc x) (tc y) acc | no ¬p = nothing
      amgu (∀' a) (∀' b) (m , acc) = σ >>= strengthen'
        where
          σ = amgu a b (m , alist-weaken acc)
          strengthen' : ∀ {ν n} → ∃ (AList (suc ν) n) → Maybe (∃ (AList ν n))
          strengthen' (m , ε) = just (m , ε)
          strengthen' (m , t' // x ◅ acc) with check' zero t'
          strengthen' (m , t' // x ◅ acc) | just z =
            (λ { (m , u) → m , z // x ◅ u }) <$> (strengthen' (m , acc))
          strengthen' (m , t' // x ◅ acc) | nothing = nothing

      -- var-var
      amgu (tvar x) (tvar y) (m , ε) with x fin≟ y
      amgu (tvar x) (tvar y) (m , ε) | yes _ = just (, ε)
      amgu (tvar x) (tvar y) (m , ε) | no _ = nothing 

      -- var-rigid / rigid-var
      amgu (mvar x) (mvar y) (m , ε) = just $ flex-flex x y
      amgu (mvar x) t (m , ε) = flex-rigid x t 

      amgu s t (m , t' // x ◅ us) with amgu (substitute σ s) (substitute σ t) (m , us)
        where σ = (t' for x )
      amgu s t (m , t' // x ◅ us) | just (m' , us') = just (m' , t' // x ◅ us')
      amgu s t (m , t' // x ◅ us) | nothing = nothing

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

{-}
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
-}
