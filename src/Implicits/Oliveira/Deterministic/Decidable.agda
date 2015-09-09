open import Prelude

module Implicits.Oliveira.Deterministic.Decidable
  (TC : Set)
  (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Data.Fin.Substitution
open import Implicits.Oliveira.Types TC _tc≟_
open import Implicits.Oliveira.Types.Unification TC _tc≟_
open import Implicits.Oliveira.Terms TC _tc≟_
open import Implicits.Oliveira.Contexts TC _tc≟_
open import Implicits.Oliveira.Substitutions TC _tc≟_
open import Implicits.Oliveira.Substitutions.Lemmas TC _tc≟_
open import Implicits.Oliveira.Deterministic.Resolution TC _tc≟_

data _,_⊢_matches_ {ν} (ρs : List (Type ν)) : Fin (suc ν) → Type ν → SimpleType ν → Set where
  mtc-tabs : ∀ {r a α} → List.map tp-weaken ρs , suc α ⊢ r matches (stp-weaken a) →
             ρs , α ⊢ ∀' r matches a
  mtc-iabs : ∀ {α a b c} → (a List.∷ ρs) , α ⊢ b matches c → ρs , α ⊢ a ⇒ b matches c
  mtc-simp : ∀ {α a b} → MGU α (simpl a) (simpl b) → ρs , α ⊢ (simpl a) matches b

data _⊢match1st_ {ν} : List (Type ν) → (a : SimpleType ν) → Set where
  m1-head : ∀ {rs} {r : Type ν} {a} → List.[] , zero ⊢ r matches a → (r List.∷ rs) ⊢match1st a
  m1-tail : ∀ {rs} {r : Type ν} {a} →
            ¬ List.[] , zero ⊢ r matches a → rs ⊢match1st a →
            (r List.∷ rs) ⊢match1st a

match : ∀ {ν} → (ρs : List (Type ν)) → (α : Fin (suc ν)) → (a : SimpleType ν) → (r : Type ν) →
        Dec (ρs , α ⊢ r matches a)
match ρs α a (simpl x) with mgu α (simpl x) (simpl a) | inspect (mgu α (simpl x)) (simpl a)
match ρs α a (simpl x) | just mgu | _ = yes (mtc-simp mgu)
match ρs α a (simpl x) | nothing | reveal[ eq ] = no (λ{ (mtc-simp x) → (mgu-sound eq) x })
match ρs α a (b ⇒ c) with match (b List.∷ ρs) α a c
match ρs α a (b ⇒ c) | yes p = yes $ mtc-iabs p
match ρs α a (b ⇒ c) | no ¬p = no (λ{ (mtc-iabs x) → ¬p x})
match ρs α a (∀' r) with match (List.map tp-weaken ρs) (suc α) (stp-weaken a) r
match ρs α a (∀' r) | yes p = yes $ mtc-tabs p
match ρs α a (∀' r) | no ¬p = no (λ{ (mtc-tabs x) → ¬p x })

_match1st_ : ∀ {ν} (Δ : ICtx ν) → (a : SimpleType ν) → Dec (Δ ⊢match1st a)
List.[] match1st a = no (λ{ () })
(x List.∷ xs) match1st a with match List.[] zero a x
(x List.∷ xs) match1st a | yes p = yes (m1-head p)
(x List.∷ xs) match1st a | no ¬p with xs match1st a
(x List.∷ xs) match1st a | no ¬p | yes p = yes (m1-tail ¬p p)
(x List.∷ xs) match1st a | no ¬p-head | no ¬p-tail =
  no (λ{ (m1-head p-head) → ¬p-head p-head ; (m1-tail _ p-tail) → ¬p-tail p-tail })

module Lemmas where

  lem-A3 : ∀ {ν n} (K : Ktx ν n) {a r} → proj₂ K ⟨ a ⟩= r → r List.∈ (proj₂ K)
  lem-A3 f = proj₁ ∘ FirstLemmas.first⟶∈

  lem-A6 : ∀ {ν} {ρs} {r : Type ν} {a α} → ρs , α ⊢ r matches a →
           ∃ λ u → (r tp/tp (TypeSubst.embed α u)) ◁ a
  lem-A6 (mtc-tabs {r = r} p) with lem-A6 p
  lem-A6 (mtc-tabs {r = r} p) | u , q = {!!} -- TODO: this should be doable, just a bit tricky
  lem-A6 (mtc-iabs p) with lem-A6 p
  lem-A6 (mtc-iabs p) | u , q = u , m-iabs q
  lem-A6 {a = a} (mtc-simp (u , eq)) = u , subst (λ e → e ◁ a) (sym eq) m-simp

  -- postulate r◁a⟶r◁weaken-a : ∀ {ν} {r : Type ν} {a} → r ◁ a → r ◁ stp-weaken a

  lem-A6' : ∀ {ν} {ρs} {r : Type ν} {a α} → r ◁ a → ρs , α ⊢ r matches a
  lem-A6' {a = a} m-simp = mtc-simp (mgu-id (simpl a)) 
  lem-A6' (m-tabs r◁a) = mtc-tabs (helper $ lem-A6' r◁a)
    where
      helper : ∀ {ν} {rs α} {r : Type (suc ν)} {b a} →
               rs , α ⊢ r tp[/tp b ] matches a →
               List.map tp-weaken rs , suc α ⊢ r matches stp-weaken a
      helper x = {!!}
  lem-A6' (m-iabs r◁a) = mtc-iabs (lem-A6' r◁a)

  -- p'haps counterintuitively the following proposition is NOT a theorem:
  -- Δ⊢ᵣa⟶Δ≢Ø : ∀ {ν n} {K : Ktx ν n} {a} → K ⊢ᵣ a → ∃ λ b → b List.∈ (proj₂ K)
  -- since [] ⊢ᵣ Nat ⇒ Nat through the r-iabs rule, but also:
  -- [] ⊢ᵣ Nat ⇒ (Nat ⇒ Nat), etc; through recursion on r-iabs

  lem-A7a : ∀ {ν} (Δ : ICtx ν) {a} → Δ ⊢match1st a → ∃ λ r → Δ ⟨ a ⟩= r
  lem-A7a List.[] ()
  lem-A7a (x List.∷ Δ) (m1-head x₁) = , (l-head x' Δ)
    where
      p = lem-A6 x₁
      x' = subst
        (λ u → u ◁ _)
        -- TODO: embed-zero-vanishes is postulated in Substitution.Lemmas
        (TypeLemmas.embed-zero-vanishes x (proj₁ p)) (proj₂ p)
  lem-A7a (r List.∷ Δ) (m1-tail ¬pr y) =
    , (l-tail (λ r◁a → ¬pr $ lem-A6' r◁a) (proj₂ $ lem-A7a Δ y))

  -- lem-A7a : ∀ {ν} (Δ : ICtx ν) {a} → Δ ⊢match1st a → ∃ λ r → Δ ⟨ a ⟩= r

open Lemmas

_⊢alg_ : ∀ {ν n} (K : Ktx ν n) → (a : Type ν) → Dec (K ⊢ᵣ a)
K ⊢alg simpl x with proj₂ K match1st x
K ⊢alg simpl x | yes p = yes (r-simp (proj₂ $ lem-A7a (proj₂ K) p) {!!})
K ⊢alg simpl x | no ¬p = no (λ{ (r-simp x₁ x₂) → {!!} })
K ⊢alg (a ⇒ b) with (a ∷K K) ⊢alg b
K ⊢alg (a ⇒ b) | yes p = yes $ r-iabs a p
K ⊢alg (a ⇒ b) | no ¬p = no (λ{ (r-iabs .a x) → ¬p x })
K ⊢alg ∀' a with (ktx-weaken K) ⊢alg a
K ⊢alg ∀' a | yes p = yes (r-tabs p)
K ⊢alg ∀' a | no ¬p = no (λ{ (r-tabs x) → ¬p x })
{-
K ⊢alg simpl x | yes (r , p) with K ⊢alg r
K ⊢alg simpl x | yes (r , p) | yes K⊢ᵣr = yes (r-simp {!p!} {!!}) -- (r-simp p {!!})
K ⊢alg simpl x | yes (r , p) | no ¬K⊢ᵣr = {!!}
K ⊢alg simpl x | no ¬p = no {!!} -- (λ{ (r-simp fst r↓x) → ¬p (, fst) })
K ⊢alg (a ⇒ b) with (a ∷K K) ⊢alg b
K ⊢alg (a ⇒ b) | yes p = yes $ r-iabs a p
K ⊢alg (a ⇒ b) | no ¬p = no (λ{ (r-iabs .a x) → ¬p x })
K ⊢alg ∀' a with (ktx-weaken K) ⊢alg a
K ⊢alg ∀' a | yes p = yes (r-tabs p)
K ⊢alg ∀' a | no ¬p = no (λ{ (r-tabs x) → ¬p x })
-}
