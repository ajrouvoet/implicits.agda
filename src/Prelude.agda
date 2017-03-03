module Prelude where

open import Data.Maybe public using (Maybe; nothing; just)
open import Data.Bool public using (Bool; true; false)
open import Data.Nat public
  using (ℕ; zero; suc; _⊔_)
  renaming ( _+_ to _N+_; _∸_ to _N-_
           ; _≤_ to _N≤_; _≥_ to _N≥_; _<_ to _N<_; _≤?_ to _N≤?_; _>_ to _N>_
           ; _≟_ to _N≟_)
open import Data.Fin public hiding (_<_)
open import Data.Fin.Properties public using () renaming (_≟_ to _fin≟_)
open import Data.Sum public hiding (map)
open import Data.Product public hiding (zip) renaming (map to pmap)
open import Data.Sum public hiding (map)
open import Data.Vec public hiding ([_])
open import Data.List as List' public using (List) hiding (module List)
open import Data.List.Any public using (Any; any; here; there; module Membership-≡)
open import Data.List.All as All' public using (All; all) hiding (module All)
open import Relation.Nullary public using (yes; no; ¬_; Dec)
open import Relation.Nullary.Decidable public using () renaming (map′ to map-dec)
open import Relation.Binary.PropositionalEquality public renaming ([_] to reveal[_])
open import Relation.Binary public using (Decidable)
open ≡-Reasoning public
open import Function public
open import Data.Empty public using (⊥; ⊥-elim)
open import Data.Unit public using (⊤)

open import Extensions.Vec public

module List where
  open List' public
  open Membership-≡ public

module All where
  open All' public
