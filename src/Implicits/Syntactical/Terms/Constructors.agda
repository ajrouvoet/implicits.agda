module Implicits.Syntactical.Terms.Constructors where

open import Prelude hiding (id)
open import Implicits.Syntactical.Terms
open import Implicits.Syntactical.WellTyped
open import Implicits.Syntactical.Substitutions
open import Implicits.Syntactical.Types.Constructors

id : nil ⊢ _ ∈ tid
id = Λ (λ' (tvar zero) (var zero))

true : nil ⊢ _ ∈ tbool
true = Λ (λ' (tvar zero) (λ' (tvar zero) (var zero)))

false : nil ⊢ _ ∈ tbool
false = Λ (λ' (tvar zero) (λ' (tvar zero) (var (suc zero))))
