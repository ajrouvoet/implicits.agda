module Prelude where

open import Data.Nat public
  using (ℕ; zero; suc; _⊔_)
  renaming ( _+_ to _N+_; _∸_ to _N-_
           ; _≤_ to _N≤_; _≥_ to _N≥_; _<_ to _N<_; _≤?_ to _N≤?_
           ; _≟_ to _N≟_)
open import Data.Fin public
open import Data.Sum public hiding (map)
open import Data.Product public hiding (zip) renaming (map to pmap)
open import Data.Vec public hiding ([_])
open import Data.List as List' public using (List)
open import Data.List.Any public using (Any; any; here; there; module Membership-≡)
open import Data.List.All as All' public using (All; all)
open import Relation.Nullary public using (yes; no; ¬_; Dec)
open import Relation.Binary.PropositionalEquality public renaming ([_] to reveal[_])
open ≡-Reasoning public
open import Function public

open import Extensions.Vec public

module List where
  open List' public
  open Membership-≡ public

module All = All'
