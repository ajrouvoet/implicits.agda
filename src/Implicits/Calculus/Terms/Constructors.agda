module Implicits.Calculus.Terms.Constructors where

open import Prelude hiding (id)
open import Implicits.Calculus.Terms
open import Implicits.Calculus.WellTyped
open import Implicits.Calculus.Substitutions
open import Implicits.Calculus.Types.Constructors

id : nil ⊢ _ ∈ tid
id = Λ (λ' (tvar zero) (var zero))

true : nil ⊢ _ ∈ tbool
true = Λ (λ' (tvar zero) (λ' (tvar zero) (var zero)))

false : nil ⊢ _ ∈ tbool
false = Λ (λ' (tvar zero) (λ' (tvar zero) (var (suc zero))))
