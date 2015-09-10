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
open import Data.Star as S 
open McBride

Bool : ∀ {n} → Type n
Bool = simpl $ tc tc-bool

Int : ∀ {n} → Type n
Int = simpl $ tc tc-int

module ex₁ where

  s : AList (suc zero) (zero)
  s = (Int // zero) ◅ ε

  s' : AList (suc (suc zero)) (suc zero)
  s' = alist-weaken s

  t : Type (suc zero)
  t = substitute (asub s') (simpl $ TVar zero →' TVar (suc zero))

open ex₁
