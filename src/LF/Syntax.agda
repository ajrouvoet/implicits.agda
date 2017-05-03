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
  unit : ∀ {n} → Term n

  -- abstractions
  ƛ : ∀ {n} → Type n → Term (suc n) → Term n

  -- application
  _·_ : ∀ {n} → Term n → Term n → Term n

data PrimE : Set where
  initFrame : PrimE
  setSlot : PrimE
  getSlot : PrimE
  setLink : PrimE

data Exp (n : ℕ) : Set where
  tm : Term n → Exp n
  --  _·*_ : (fn : ℕ) → (as : List (Term n)) → Exp n
  lett : (x : Exp n) → (e : Exp (suc n)) → Exp n
  prim : PrimE → Exp n

data PrimT : Set where
  Frame : PrimT
  Decl : PrimT
  Path : PrimT
  Edge : PrimT

infixl 20 _[_]
data Type where
  𝕜 : ∀ {n} → ℕ → Type n
  Π : ∀ {n} → (A : Type n) → (B : Type (suc n)) → Type n
  _[_] : ∀ {n} → (T : Type n) → (x : Term n) → Type n
  Prim : ∀ {n} → PrimT → Type n

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

  𝕜 x tp/ s = 𝕜 x
  Π A B tp/ s = Π (A tp/ s) (B tp/ (s ↑))
  (A [ x ]) tp/ s = (A tp/ s) [ x / s ]
  Prim x tp/ s = Prim x

  _kind/_ : ∀ {n n'} → Kind n → Sub T n n' → Kind n'
  ★ kind/ s = ★
  Π A K kind/ s = Π (A tp/ s) (K kind/ (s ↑))

  _exp/_ : ∀ {n n'} → Exp n → Sub T n n' → Exp n'
  tm x exp/ s = tm (x / s)
  -- (fn ·* as) exp/ s = fn ·* (map (flip _/_ s) as)
  lett x e exp/ s = lett (x exp/ s) (e exp/ (s ↑))
  prim x exp/ s = prim x

  open Application (record { _/_ = _/_ }) using (_/✶_)

tmSubst : TermSubst Term
tmSubst = record { var = var; app = App._/_ }

open TermSubst tmSubst hiding (var) public

open App termLift using (_exp/_; _tp/_; _kind/_) public
