open import Prelude

module Effects.Terms (EC : Set) (_ec≟_ : Decidable {A = EC} _≡_) where

infixl 8 _∪_ _→[_]_ _·_ _[_]

data Effect (η : ℕ) : Set where

  evar : Fin η → Effect η
  has : EC → Effect η
  H : Effect (suc η) → Effect η

private
  ≡evar : ∀ {η x y} → evar {η} x ≡ evar {η} y → x ≡ y
  ≡evar refl = refl

  ≡H : ∀ {η x y} → H {η} x ≡ H {η} y → x ≡ y
  ≡H refl = refl

  ≡has : ∀ {η x y} → has {η} x ≡ has {η} y → x ≡ y
  ≡has refl = refl

-- decidable equality for effects
_≟_ : ∀ {η} → Decidable {A = Effect η} _≡_
evar x ≟ evar y with x fin≟ y
evar x ≟ evar y | yes x≡y = yes $ cong evar x≡y
evar x ≟ evar y | no x≢y = no (λ eq → x≢y (≡evar eq))
evar x ≟ has y = no (λ ())
evar x ≟ H r = no (λ ())
has x ≟ evar x₁ = no (λ ())
has x ≟ has y with x ec≟ y 
has x ≟ has y | yes x≡y = yes $ cong has x≡y
has x ≟ has y | no x≢y = no (λ eq → x≢y (≡has eq))
has x ≟ H r = no (λ ())
H l ≟ evar x = no (λ ())
H l ≟ has x = no (λ ())
H l ≟ H r with l ≟ r
H l ≟ H r | yes l≡r = yes $ cong H l≡r
H l ≟ H r | no l≢r = no (λ eq → l≢r (≡H eq))

Effects : ℕ → Set
Effects η = List (Effect η)

_&_ : ∀ {η} → Effect η → Effects η → Effects η
e & es with (any (_≟_ e) es)
e & es | yes p = es
e & es | no ¬p = e List.∷ es

_∪_ : ∀ {η} → Effects η → Effects η → Effects η
List.[] ∪ r = r
(x List.∷ l) ∪ r = x & (l ∪ r)

pure : ∀ {η} → Effects η
pure = List.[]

H' : ∀ {η} → Effects (suc η) → Effects η
H' es = List.map H es

data Type (ν η : ℕ) : Set where

  unit : Type ν η
  tvar : Fin ν → Type ν η
  _→[_]_ : Type ν η → Effects η → Type ν η → Type ν η

  -- type abstraction
  ∀' : Type (suc ν) η → Type ν η

  -- effect abstraction
  H : Type ν (suc η) → Type ν η

data Term (ν η n : ℕ) : Set where

  -- unit value
  tt : Term ν η n

  -- some primitives that perform effectful computations
  print : Term ν η n -- io
  throw : Term ν η n -- exception
  write : Term ν η n -- write heap
  read  : Term ν η n -- read heap

  -- variables
  var : Fin n → Term ν η n

  -- term abstraction & application
  λ'  : Type ν η → Term ν η (suc n) → Term ν η n
  _·_ : Term ν η n → Term ν η n → Term ν η n

  -- type abstraction & application
  Λ    : Term (suc ν) η n → Term ν η n
  _[_] : Term ν η n → Type ν η → Term ν η n

  -- effect abstraction & applixation
  H   : Term ν (suc η) n → Term ν η n
  _!_ : Term ν η n → Effects η → Term ν η n

Ctx : ℕ → ℕ → ℕ → Set
Ctx ν η n = Vec (Type ν η) n
