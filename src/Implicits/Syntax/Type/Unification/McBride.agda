open import Prelude hiding (id; _>>=_)

module Implicits.Syntax.Type.Unification.McBride where

open import Implicits.Syntax
open import Implicits.Syntax.MetaType
open import Data.Vec.Properties
open import Data.Nat as N using ()
open import Data.Nat.Properties.Simple

open import Category.Monad

open import Data.Maybe as Maybe using (monad; functor)
open import Level using () renaming (zero to level₀)
open RawMonad {level₀} monad using (_>>=_; return)
open import Category.Functor
open RawFunctor {level₀} functor
open import Data.Star hiding (_>>=_)

open import Data.Fin.Substitution
open import Implicits.Substitutions
open import Implicits.Substitutions.Lemmas

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

check' : ∀ {ν} → Fin (suc ν) → Type (suc ν) → Maybe (Type ν)
check' n (simpl (tvar m)) = (λ n → simpl (tvar n)) <$> (thick n m)
check' n (simpl (tc x)) = just (simpl (tc x))
check' n (simpl (a →' b)) with check' n a | check' n b
check' n (simpl (a →' b)) | just x | just y = just (simpl (x →' y))
check' n (simpl (a →' b)) | _ | nothing = nothing
check' n (simpl (a →' b)) | nothing | _ = nothing
check' n (a ⇒ b) with check' n a | check' n b
check' n (a ⇒ b) | just x | just y = just (x ⇒ y)
check' n (a ⇒ b) | _ | nothing = nothing
check' n (a ⇒ b) | nothing | _ = nothing
check' n (∀' t) with check' (suc n) t
check' n (∀' t) | just x = just (∀' x)
check' n (∀' t) | nothing = nothing

substitute : {ν m n : ℕ} → (Fin m → MetaType n ν) → MetaType m ν → MetaType n ν
substitute f a = a M./ (tabulate f)

_for_ : ∀ {n ν} → Type ν → Fin (suc n) → Fin (suc n) → MetaType n ν
_for_ t' x y with thick x y
_for_ t' x y | just y' = simpl (mvar y')
_for_ t' x y | nothing = to-meta t'

data ASub (ν : ℕ) : ℕ → ℕ → Set where
  _//_ : ∀ {m} → (t' : Type ν) → Fin (suc m) → ASub ν (suc m) m

AList : ℕ → ℕ → ℕ → Set
AList ν m n = Star (ASub ν) m n

asub-tp-weaken : ∀ {ν m n} → ASub ν m n → ASub (suc ν) m n
asub-tp-weaken (t' // x) = tp-weaken t' // x

asub-weaken : ∀ {ν m n} → ASub ν m n → ASub ν (suc m) (suc n)
asub-weaken (t' // x) = t' // (suc x)

alist-weaken : ∀ {ν m n} → AList ν m n → AList (suc ν) m n
alist-weaken s = gmap Prelude.id (λ x → asub-tp-weaken x) s

_◇_ : ∀ {l m n ν} → (Fin m → MetaType n ν) → (Fin l → MetaType m ν) → (Fin l → MetaType n ν)
f ◇ g = substitute f ∘ g

asub' : ∀ {ν m n} → (σ : AList ν m n) → Fin m → MetaType n ν
asub' ε = λ n → simpl (mvar n)
asub' (t' // x ◅ y) =  asub' y ◇ (t' for x)

asub : ∀ {ν m n} → (σ : AList ν m n) → Sub (flip MetaType ν) m n
asub s = tabulate (asub' s)

mgu : ∀ {m ν} → MetaType m ν → Type ν → Maybe (∃ (AList ν m))
mgu {ν} s t = amgu s t (ν , ε)
  where
    amgu : ∀ {ν m} (s : MetaType m ν) → (t : Type ν)→ ∃ (AList ν m) → Maybe (∃ (AList ν m))
    -- non-matching constructors
    amgu (simpl (tc x)) (_ ⇒ _) acc = nothing
    amgu (simpl (tc _)) (∀' _) x = nothing
    amgu (simpl (tc x)) (simpl (_ →' _)) acc = nothing
    amgu (simpl (tc _)) (simpl (tvar _)) x = nothing
    amgu (simpl (_ →' _)) (∀' _) x = nothing
    amgu (simpl (_ →' _)) (_ ⇒ _) x = nothing
    amgu (simpl (_ →' _)) (simpl (tc _)) acc = nothing
    amgu (simpl (_ →' _)) (simpl (tvar _)) x = nothing
    amgu (_ ⇒ _) (simpl x) acc = nothing
    amgu (_ ⇒ _) (∀' _) x = nothing
    amgu (∀' _) (_ ⇒ _) x = nothing
    amgu (∀' _) (simpl _) x = nothing
    amgu (simpl (tvar _)) (_ ⇒ _) x = nothing
    amgu (simpl (tvar _)) (∀' _) x = nothing
    amgu (simpl (tvar _)) (simpl (tc _)) x = nothing
    amgu (simpl (tvar _)) (simpl (_ →' _)) acc = nothing

    -- matching constructors
    amgu (a ⇒ b) (a' ⇒ b') acc = _>>=_ (amgu b b' acc) (amgu a a')
    amgu (simpl (a →' b)) (simpl (a' →' b')) acc = _>>=_ (amgu b b' acc) (amgu a a')
    amgu (simpl (tc x)) (simpl (tc y)) acc with x N≟ y 
    amgu (simpl (tc x)) (simpl (tc y)) acc | yes p = just (, ε)
    amgu (simpl (tc x)) (simpl (tc y)) acc | no ¬p = nothing
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
    amgu ((simpl (tvar x))) ((simpl (tvar y))) (m , ε) with x fin≟ y
    amgu ((simpl (tvar x))) ((simpl (tvar y))) (m , ε) | yes _ = just (, ε)
    amgu ((simpl (tvar x))) ((simpl (tvar y))) (m , ε) | no _ = nothing 

    -- var-rigid / rigid-var
    amgu (simpl (mvar ())) t (zero , ε)
    amgu (simpl (mvar x)) t (suc m , ε) = just (m , t // x ◅ ε)

    amgu s t (m , t' // x ◅ us) with amgu (substitute (t' for x) s) t (m , us)
    amgu s t (m , t' // x ◅ us) | just (m' , us') = just (m' , t' // x ◅ us')
    amgu s t (m , t' // x ◅ us) | nothing = nothing
