open import Prelude hiding (id; _>>=_)

module Implicits.Syntax.Type.Unification where

open import Data.Maybe as Maybe
open import Data.Unit
open import Implicits.Syntax
open import Implicits.Syntax.Type.Unification.McBride as McBride using (
  substitute; asub; AList; _//_) public
open import Data.Vec.Properties
open import Data.Nat as N using ()
open import Data.Nat.Properties.Simple
open import Category.Monad

open import Data.Fin.Substitution
open import Implicits.Substitutions
open import Implicits.Syntax.MetaType public
open import Implicits.Substitutions.Lemmas
open McBride using (substitute; asub; AList; ASub; _//_; asub-weaken) public

private
  module M = MetaTypeMetaSubst
  module T = MetaTypeTypeSubst

-- Just a bit stricter than mcbride.mgu
-- We require here as well that all meta variables are instantiated
-- (this is equivalent to the ⊢unamb constraint in Oliveira)
mgu : ∀ {m ν} (a : MetaType m ν) → (b : SimpleType ν) → Maybe (Sub (flip MetaType ν) m zero)
mgu a b with McBride.mgu a (simpl b)
mgu a b | just (zero , u) = just (asub u)
mgu a b | just (suc m , _) = nothing
mgu a b | nothing = nothing

Unifier : ∀ {m ν} → (MetaType m ν) → SimpleType ν → (Sub (flip MetaType ν) m zero) → Set
Unifier {m} a b u = from-meta (a M./ u) ≡ (simpl b)

Unifiable : ∀ {m ν} → (MetaType m ν) → SimpleType ν → Set
Unifiable a τ = ∃ (Unifier a τ)

◁-Unifiable : ∀ {m ν} → MetaType m ν → SimpleType ν → Set
◁-Unifiable x τ = Unifiable (x M.◁m) τ

meta-weaken = M.weaken
smeta-weaken = M.smeta-weaken
open-meta = M.open-meta
