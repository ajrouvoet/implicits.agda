open import Prelude hiding (lift; Fin′; subst)

module Implicits.Syntax
  (TC : Set)
  (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Implicits.Syntax.Type TC _tc≟_ public
open import Implicits.Syntax.Term TC _tc≟_ public
open import Implicits.Syntax.Context TC _tc≟_ public
