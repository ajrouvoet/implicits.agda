open import Prelude 

module Implicits.Resolution.Scala.Type where

open import Implicits.Syntax
open import Implicits.Substitutions
open import Implicits.Substitutions.Lemmas.Type
open import Implicits.Substitutions.Type as TS using () 

-- predicate on types to limit them to non-rule types
-- (as those don't exist in Scala currently)

mutual
  data ScalaSimpleType {ν} : SimpleType ν → Set where
    tc   : (c : ℕ) → ScalaSimpleType (tc c)
    tvar : (n : Fin ν) → ScalaSimpleType (tvar n)
    _→'_ : ∀ {a b} → ScalaType a → ScalaType b → ScalaSimpleType (a →' b)

  data ScalaType {ν} : Type ν → Set where
    simpl : ∀ {τ} → ScalaSimpleType {ν} τ → ScalaType (simpl τ)
    ∀'    : ∀ {a} → ScalaType a → ScalaType (∀' a)

data ScalaRule {ν} : Type ν → Set where
  idef  : ∀ {a b} → ScalaType a → ScalaType b → ScalaRule (a ⇒ b)
  ival  : ∀ {a} → ScalaType a → ScalaRule a
  
ScalaICtx : ∀ {ν} → ICtx ν → Set
ScalaICtx Δ = All ScalaRule Δ

mutual

  weaken-scalastype : ∀ {ν} k {a : SimpleType (k N+ ν)} → ScalaSimpleType a →
                      ScalaType (a TS.simple/ (TS.wk TS.↑⋆ k))
  weaken-scalastype k (tc c) = simpl (tc c)
  weaken-scalastype k (tvar n) = Prelude.subst
    (λ z → ScalaType z)
    (sym $ var-/-wk-↑⋆ k n)
    (simpl (tvar (lift k suc n)))
  weaken-scalastype k (a →' b) = simpl ((weaken-scalatype k a) →' (weaken-scalatype k b))

  weaken-scalatype : ∀ {ν} k {a : Type (k N+ ν)} → ScalaType a → ScalaType (a TS./ TS.wk TS.↑⋆ k)
  weaken-scalatype k (simpl {τ} x) = weaken-scalastype k x
  weaken-scalatype k (∀' p) = ∀' (weaken-scalatype (suc k) p)

weaken-scalarule : ∀ {ν} k {a : Type (k N+ ν)} → ScalaRule a → ScalaRule (a TS./ (TS.wk TS.↑⋆ k))
weaken-scalarule k (idef x y) = idef (weaken-scalatype k x) (weaken-scalatype k y)
weaken-scalarule k (ival x) = ival (weaken-scalatype k x)

weaken-scalaictx : ∀ {ν} {Δ : ICtx ν} → ScalaICtx Δ → ScalaICtx (ictx-weaken Δ)
weaken-scalaictx All.[] = All.[]
weaken-scalaictx (px All.∷ ps) = weaken-scalarule zero px All.∷ weaken-scalaictx ps
