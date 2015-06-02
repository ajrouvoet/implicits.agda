module Prelude where

open import Data.Nat public
  using (ℕ; zero; suc)
  renaming ( _+_ to _N+_; _∸_ to _N∸_
           ; _≤_ to _N≤_; _≥_ to _N≥_; _<_ to _N<_; _≤?_ to _N≤?_
           ; _≟_ to _N≟_)
open import Data.Fin public
open import Data.Sum public hiding (map)
open import Data.Product public hiding (map; zip)
open import Data.Vec public hiding ([_])
open import Relation.Nullary public using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality public hiding ([_])
open import Function public
