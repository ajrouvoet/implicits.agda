module LF.Syntax where

open import Prelude
open import Data.Vec hiding ([_]; map)
open import Data.List hiding ([_])

data Kind : (n : ℕ) → Set
data Term : (n : ℕ) → Set
data Type : (n : ℕ) → Set

infixl 30 _·_
data Term where
  -- variables
  var : ∀ {n} → Fin n → Term n
  con : ∀ {n} → ℕ → Term n
  loc : ∀ {n} → ℕ → Term n
  unit : ∀ {n} → Term n

  -- abstractions
  ƛ : ∀ {n} → Type n → Term (suc n) → Term n

  -- application
  _·_ : ∀ {n} → Term n → Term n → Term n

data Exp (n : ℕ) : Set where
  tm : Term n → Exp n
  --  _·*_ : (fn : ℕ) → (as : List (Term n)) → Exp n
  lett : (x : Exp n) → (e : Exp (suc n)) → Exp n
  ref : Exp n → Exp n
  !_ : Exp n → Exp n
  _≔_ : Exp n → Exp n → Exp n

infixl 20 _[_]
data Type where
  𝕜 : ∀ {n} → ℕ → Type n
  Π : ∀ {n} → (A : Type n) → (B : Type (suc n)) → Type n
  _[_] : ∀ {n} → (T : Type n) → (x : Term n) → Type n
  Ref : ∀ {n} → (A : Type n) → Type n
  Unit : ∀ {n} → Type n

data Kind where
  ★ : ∀ {n} → Kind n
  Π : ∀ {n} → (A : Type n) → (K : Kind (suc n)) → Kind n

Store : ℕ → Set
Store n = List (Term n)

open import Data.Fin.Substitution

module App {T} (l : Lift T Term) where
  open Lift l

  _/_ : ∀ {n n'} → Term n → Sub T n n' → Term n'
  _tp/_ : ∀ {n n'} → Type n → Sub T n n' → Type n'

  var x / s = lift $ lookup x s
  ƛ A t / s = ƛ (A tp/ s) (t / (s ↑))
  (f · e) / s = (f / s) · (e / s)
  unit / s = unit
  con x / s = con x
  loc x / s = loc x

  𝕜 x tp/ s = 𝕜 x
  Π A B tp/ s = Π (A tp/ s) (B tp/ (s ↑))
  (A [ x ]) tp/ s = (A tp/ s) [ x / s ]
  (Ref A) tp/ s = Ref (A tp/ s)
  Unit tp/ s = Unit

  _kind/_ : ∀ {n n'} → Kind n → Sub T n n' → Kind n'
  ★ kind/ s = ★
  Π A K kind/ s = Π (A tp/ s) (K kind/ (s ↑))

  _exp/_ : ∀ {n n'} → Exp n → Sub T n n' → Exp n'
  tm x exp/ s = tm (x / s)
  lett x e exp/ s = lett (x exp/ s) (e exp/ (s ↑))
  ref x exp/ s = ref (x exp/ s)
  (! x) exp/ s = ! (x exp/ s)
  (y ≔ x) exp/ s = (y exp/ s) ≔ (x exp/ s)

  open Application (record { _/_ = _/_ }) using (_/✶_)

tmSubst : TermSubst Term
tmSubst = record { var = var; app = App._/_ }

open TermSubst tmSubst hiding (var) public

open App termLift using (_exp/_; _tp/_; _kind/_) public
