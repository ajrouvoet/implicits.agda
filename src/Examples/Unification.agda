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
open import Implicits.Oliveira.Types.Unification.McBride TC _tc≟_ as McBride using ()
open import Data.Star as S 
open import Data.Maybe

open import Level using () renaming (zero to level₀)
open import Data.Maybe using (monad; functor)
open import Category.Functor
open RawFunctor {level₀} functor

module M = MetaTypeMetaSubst
module T = MetaTypeTypeSubst

Bool : ∀ {n} → Type n
Bool = simpl (tc tc-bool)

Int : ∀ {n} → Type n
Int = simpl (tc tc-int)

module ex₂ where
  -- mgu test for simple 2 variable substitution

  a : MetaType (suc (suc zero)) (suc zero)
  a = open-meta $ open-meta $ to-meta $ (simpl ((simpl (tvar zero)) →' (simpl (simpl (tvar (suc zero)) →' simpl (tvar (suc (suc zero)))))))

  b : SimpleType (suc zero)
  b = Int →' (simpl (Int →' simpl (tvar zero)))

  s = mgu a b

  u = asub (proj₁ $ from-just s)

  unifies : a M./ u ≡ (simpl (to-smeta b))
  unifies = refl

module ex₃ where
  -- mgu test for simple 1 variable substitution
  -- (limited α)

  a : MetaType (suc zero) (suc zero)
  a = open-meta (to-meta (∀' (simpl ((simpl (tvar zero)) →' simpl (tvar (suc zero))))))

  b : SimpleType (suc zero)
  b = Int →' Int

  s : mgu a b ≡ nothing
  s = refl

module ex₄ where
  -- with ∀' in there somewhere

  a : MetaType (suc zero) (suc zero)
  a = simpl ((∀' (s-mvar zero)) →' (s-tc tc-int))

  -- won't unify with a because we'd need to instantiate s-mvar zero with
  -- a s-tvar that's not yet introduced
  b : SimpleType (suc zero)
  b = (∀' (simpl (tvar zero))) →' Int

  s : mgu a b ≡ nothing
  s = refl

module ex₅ where
  -- renaming example

  a : MetaType (suc (suc zero)) (suc zero)
  a = (s-mvar zero) ⇒ (s-mvar (suc zero))

  b : Type (suc zero)
  b = (simpl (tvar (zero))) ⇒ (simpl (tvar zero))

  s : is-just (McBride.mgu a b) ≡ true
  s = refl

open ex₅
