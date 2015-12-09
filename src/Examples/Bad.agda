{-# OPTIONS --no-positivity-check #-}
open import Prelude hiding (id; Bool; _∷_; [])

module Examples.Bad where

data TC : Set where
  tc-int : TC
  tc-bool : TC
  tc-char : TC

_tc≟_ : (a b : TC) → Dec (a ≡ b)
tc-int tc≟ tc-int = yes refl
tc-int tc≟ tc-bool = no (λ ())
tc-bool tc≟ tc-int = no (λ ())
tc-bool tc≟ tc-bool = yes refl
tc-int tc≟ tc-char = no (λ ())
tc-bool tc≟ tc-char = no (λ ())
tc-char tc≟ tc-int = no (λ ())
tc-char tc≟ tc-bool = no (λ ())
tc-char tc≟ tc-char = yes refl

open import Implicits.Oliveira.Types TC _tc≟_
open import Implicits.Oliveira.Terms TC _tc≟_
open import Implicits.Oliveira.Contexts TC _tc≟_
open import Implicits.Oliveira.WellTyped TC _tc≟_
open import Implicits.Oliveira.Substitutions TC _tc≟_
open import Implicits.Oliveira.Types.Unification TC _tc≟_
open import Implicits.Improved.Undecidable.Resolution TC _tc≟_
open import Data.Maybe
open import Data.List
open import Extensions.ListFirst

Bool : ∀ {n} → Type n
Bool = simpl (tc tc-bool)

Int : ∀ {n} → Type n
Int = simpl (tc tc-int)

Char : ∀ {n} → Type n
Char = simpl (tc tc-char)

module Ex₀ where

  data Bad : Set where
    bad : ¬ Bad → Bad

  getFun : Bad → ¬ Bad
  getFun (bad x) = x

  omega : Bad → ⊥
  omega b = getFun b b

  loop : ⊥
  loop = omega (bad omega)

module Ex₁ where

  Δ : ICtx zero
  Δ = Bool ⇒ Bool ∷ Bool ∷ []

  Bad : Set
  Bad = Δ ⊢ (Bool ⇒ Bool ) ↓ (tc tc-bool)

  getFun : Bad → ¬ Bad
  getFun (i-iabs (r-simp (here p ._)) x₁) = {!!} 
  getFun (i-iabs (r-simp (there ._ f x)) y) = f

  omega : Bad → ⊥
  omega b = getFun b b

  bad : ¬ Bad → Bad
  bad ¬x = i-iabs (r-simp (there _ ¬x (here (i-simp (tc tc-bool)) []))) (i-simp (tc tc-bool))

  loop : ⊥
  loop = omega (bad omega)

