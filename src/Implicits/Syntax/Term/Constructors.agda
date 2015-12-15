module Implicits.Oliveira.Terms.Constructors (TC : Set) where

open import Prelude hiding (id)
open import Implicits.Oliveira.WellTyped TC
open import Implicits.Oliveira.Substitutions TC
open import Implicits.Oliveira.Types.Constructors TC

id : ∀ {n} → nil ⊢ _ ∈ tid {n}
id = Λ (λ' (tvar zero) (var zero))

true : nil ⊢ _ ∈ tbool
true = Λ (λ' (tvar zero) (λ' (tvar zero) (var zero)))

false : nil ⊢ _ ∈ tbool
false = Λ (λ' (tvar zero) (λ' (tvar zero) (var (suc zero))))