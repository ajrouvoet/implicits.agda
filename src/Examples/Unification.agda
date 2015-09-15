open import Prelude hiding (id; Bool)

module Examples.Unification where

data TC : Set where
  tc-int : TC
  tc-bool : TC

_tc≟_ : (a b : TC) → Dec (a ≡ b)
tc-int tc≟ tc-int = yes refl
tc-int tc≟ tc-bool = no (λ ())
tc-bool tc≟ tc-int = no (λ ())
tc-bool tc≟ tc-bool = yes refl

open import Implicits.Oliveira.Types TC _tc≟_
open import Implicits.Oliveira.Terms TC _tc≟_
open import Implicits.Oliveira.Contexts TC _tc≟_
open import Implicits.Oliveira.WellTyped TC _tc≟_
open import Implicits.Oliveira.Substitutions TC _tc≟_
open import Implicits.Oliveira.Types.Unification TC _tc≟_
open import Implicits.Oliveira.Types.Unification.Types TC _tc≟_
open import Data.Star as S 
open import Data.Maybe
open McBride

open import Level using () renaming (zero to level₀)
open import Data.Maybe using (monad; functor)
open import Category.Functor
open RawFunctor {level₀} functor
open MetaTypeMetaSubst using (open-meta)

module M = MetaTypeMetaSubst

Bool : ∀ {n} → Type n
Bool = simpl $ tc tc-bool

Int : ∀ {n} → Type n
Int = simpl $ tc tc-int

module ex₁ where

  s : AList zero (suc zero) (zero)
  s = ((tc tc-int) // zero) ◅ ε

  s' : AList (suc zero) (suc zero) zero
  s' = alist-weaken s

  t : MetaType zero (suc zero)
  t = substitute (asub s') (fork rul (mvar zero) (mvar zero))

module ex₂ where
  -- mgu test for simple 2 variable substitution

  a : MetaType zero (suc (suc (suc zero)))
  a = to-meta $ (∀' (∀' (simpl $ (TVar zero) →' (simpl $ TVar (suc zero) →' TVar (suc (suc zero))))))

  b : MetaType (suc (suc zero)) (suc (suc (suc zero)))
  b = to-meta (simpl $ Int →' (simpl $ Int →' TVar zero))

  s : is-just (mgu (open-meta $ open-meta a) b) ≡ true
  s = refl

module ex₃ where
  -- mgu test for simple 1 variable substitution
  -- (limited α)

  a : MetaType (suc zero) (suc zero)
  a = open-meta (to-meta (∀' (simpl $ (TVar zero) →' TVar (suc zero))))

  b : MetaType (suc zero) (suc zero)
  b = M.weaken $ to-meta (simpl $ Int →' Int)

  s : mgu a b ≡ nothing
  s = refl

module ex₅ where
  -- renaming example

  a : MetaType (suc (suc zero)) zero
  a = fork rul (mvar zero) (mvar (suc zero))

  b : MetaType (suc (suc zero)) zero
  b = fork rul (mvar (suc zero)) (mvar zero)

  s = mgu a b 

open ex₅
