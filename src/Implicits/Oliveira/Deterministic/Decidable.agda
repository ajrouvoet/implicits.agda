open import Prelude

module Implicits.Oliveira.Deterministic.Decidable
  (TC : Set)
  (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Data.Fin.Substitution
open import Implicits.Oliveira.Types TC _tc≟_
open import Implicits.Oliveira.Terms TC _tc≟_
open import Implicits.Oliveira.Contexts TC _tc≟_
open import Implicits.Oliveira.Substitutions TC _tc≟_
open import Implicits.Oliveira.Substitutions.Lemmas TC _tc≟_
open import Implicits.Oliveira.Deterministic.Resolution TC _tc≟_
open import Implicits.Oliveira.Types.Unification TC _tc≟_
open import Data.Star hiding (map)

MICtx : ℕ → ℕ → Set
MICtx m ν = List (MetaType m ν)

private
  module M = MetaTypeMetaSubst
  module T = MetaTypeTypeSubst

{-
{-# NO_TERMINATION_CHECK #-}
_,_amatch_ : ∀ {m ν} → (MetaType m ν) → (ρs : MICtx m ν) → (τ : SimpleType ν) → Maybe (ICtx ν)
(a ⇒ b) , ρs amatch τ = b , a List.∷ ρs amatch τ
∀' x , ρs amatch τ = open-meta x , (List.map meta-weaken ρs) amatch τ
(simpl x) , ρs amatch τ with mgu (simpl x) τ
(simpl x) , ρs amatch τ | just (u , proj₂) =
  just $ List.map (λ r → from-meta $ substitute (asub u) r) ρs
(simpl x) , ρs amatch τ | nothing = nothing

_match_ : ∀ {ν} → (Type ν) → (SimpleType ν) → Maybe (ICtx ν)
r match a = (to-meta {zero} r) , List.[] amatch a 

{-# NO_TERMINATION_CHECK #-}
lem-a6 : ∀ {m ν} {ρs ρs'} (a : MetaType m ν) (τ : SimpleType ν) → a , ρs amatch τ ≡ just ρs' →
  (∃ λ (u : AList ν m zero) → (from-meta $ substitute (asub u) a) ◁ τ) 
lem-a6 {ρs = ρs} (a ⇒ b) τ m
  with _,_amatch_ b (a List.∷ ρs) τ | inspect (_,_amatch_ b (a List.∷ ρs)) τ 
lem-a6 (a ⇒ b) τ refl | ._ | reveal[ eq ] with lem-a6 b τ eq
lem-a6 (a ⇒ b) τ refl | ._ | reveal[ eq ] | u , b/u◁τ = u , (m-iabs b/u◁τ)
lem-a6 {ρs = ρs} (∀' a) τ m 
  with open-meta a , (List.map meta-weaken ρs) amatch τ | inspect (_,_amatch_ (open-meta a) (List.map meta-weaken ρs)) τ 
lem-a6 (∀' a) τ refl | ._ | reveal[ eq ] with lem-a6 (open-meta a) τ eq
lem-a6 (∀' a) τ refl | ._ | reveal[ eq ] | (t' // x ◅ u , b/u◁τ) = {!!} -- {!u!} , (m-tabs {!!})
lem-a6 (simpl x) τ m with mgu (simpl x) τ | inspect (mgu (simpl x)) τ
lem-a6 (simpl x) τ refl | just (u , proj₂) | reveal[ eq ] = 
  u , subst (λ u → u ◁ τ) (sym $ mgu-unifies (simpl x) τ {!!}) m-simp
lem-a6 (simpl x) τ () | nothing

_match1st_ : ∀ {ν} (Δ : ICtx ν) → (a : SimpleType ν) → Maybe (Type ν × ICtx ν)
List.[] match1st a = nothing
(x List.∷ Δ) match1st a with x match a
(x List.∷ Δ) match1st a | just z = just (x , z)
(x List.∷ Δ) match1st a | nothing = Δ match1st a

_⊢alg_ : ∀ {ν n} (K : Ktx ν n) → (a : Type ν) → Dec (K ⊢ᵣ a)
(Γ , Δ) ⊢alg simpl x with Δ match1st x
(Γ , Δ) ⊢alg simpl x | just (proj₁ , proj₂) = {!!}
(Γ , Δ) ⊢alg simpl x | nothing = {!!}
K ⊢alg (a ⇒ b) with (a ∷K K) ⊢alg b
K ⊢alg (a ⇒ b) | yes p = yes $ r-iabs a p
K ⊢alg (a ⇒ b) | no ¬p = no (λ{ (r-iabs .a x) → ¬p x })
K ⊢alg ∀' a with (ktx-weaken K) ⊢alg a
K ⊢alg ∀' a | yes p = yes (r-tabs p)
K ⊢alg ∀' a | no ¬p = no (λ{ (r-tabs p) → ¬p p })

-}
module relational where

  data _⊢_amatch_ {m ν} : (ρs : MICtx m ν) → MetaType m ν → SimpleType ν → Set where
    mtc-tabs : ∀ {r ρs a} → (List.map meta-weaken ρs) ⊢ (open-meta r) amatch a →
                ρs ⊢ ∀' r amatch a
    mtc-iabs : ∀ {ρs a b c} → (a List.∷ ρs) ⊢ b amatch c → ρs ⊢ a ⇒ b amatch c
    mtc-simp : ∀ {ρs a b} → Unifiable (simpl a) b → ρs ⊢ (simpl a) amatch b

  _⊢match_ : ∀ {ν} → (Type ν) → (SimpleType ν) → Set
  r ⊢match a = List.[] ⊢ (to-meta {zero} r) amatch a

  data _⊢match1st_ {ν} : List (Type ν) → (a : SimpleType ν) → Set where
    m1-head : ∀ {rs} {r : Type ν} {a} → r ⊢match a → (r List.∷ rs) ⊢match1st a
    m1-tail : ∀ {rs} {r : Type ν} {a} → ¬ r ⊢match a → rs ⊢match1st a → (r List.∷ rs) ⊢match1st a

  gather : ∀ {ν} {ρs : List (Type ν)} {a} → ρs ⊢match1st a → List (Type ν)
  gather (m1-head x) = gather' x
    where
        gather' : ∀ {m ν} {ρs : MICtx m ν} {r a} → ρs ⊢ r amatch a → List (Type ν)
        gather' (mtc-tabs x) = gather' x
        gather' (mtc-iabs x) = gather' x
        gather' {ρs = ρs} (mtc-simp {a = a} {b = b} u) =
                (List.map (λ r → from-meta $ substitute (asub (proj₁ u)) r) ρs)
  gather (m1-tail ¬x xs) = gather xs

  {-# NO_TERMINATION_CHECK #-}
  amatch : ∀ {m ν} → (ρs : MICtx m ν) → (r : MetaType m ν) (a : SimpleType ν) →
            Dec (ρs ⊢ r amatch a)
  amatch ρs (simpl x) a with mgu (simpl x) a | inspect (mgu (simpl x)) a
  amatch ρs (simpl x) a | just mgu | _ = yes (mtc-simp mgu)
  amatch ρs (simpl x) a | nothing | reveal[ eq ] =
    no (λ{ (mtc-simp p) → (mgu-sound (simpl x) a eq) p})
  amatch ρs (b ⇒ c) a with amatch (b List.∷ ρs) c a
  amatch ρs (b ⇒ c) a | yes p = yes $ mtc-iabs p
  amatch ρs (b ⇒ c) a | no ¬p = no (λ{ (mtc-iabs x) → ¬p x})
  amatch ρs (∀' r) a with amatch (List.map meta-weaken ρs) (open-meta r) a
  amatch ρs (∀' r) a | yes p = yes $ mtc-tabs p
  amatch ρs (∀' r) a | no ¬p = no (λ{ (mtc-tabs x) → ¬p x })

  match : ∀ {ν}  → (r : Type ν) → (a : SimpleType ν) → Dec (r ⊢match a)
  match r a = amatch List.[] (to-meta {zero} r) a

  _match1st_ : ∀ {ν} (Δ : ICtx ν) → (a : SimpleType ν) → Dec (Δ ⊢match1st a)
  List.[] match1st a = no (λ{ () })
  (x List.∷ xs) match1st a with match x a
  (x List.∷ xs) match1st a | yes p = yes (m1-head p)
  (x List.∷ xs) match1st a | no ¬p with xs match1st a
  (x List.∷ xs) match1st a | no ¬p | yes p = yes (m1-tail ¬p p)
  (x List.∷ xs) match1st a | no ¬p-head | no ¬p-tail =
    no (λ{ (m1-head p-head) → ¬p-head p-head ; (m1-tail _ p-tail) → ¬p-tail p-tail })

  module Lemmas where

    lem-A3 : ∀ {ν n} (K : Ktx ν n) {a r} → proj₂ K ⟨ a ⟩= r → r List.∈ (proj₂ K)
    lem-A3 f = proj₁ ∘ FirstLemmas.first⟶∈

    lem-A6 : ∀ {m ν} {ρs} {a : MetaType m ν} {τ : SimpleType ν} → ρs ⊢ a amatch τ →
             (∃ λ (u : AList ν m zero) → (from-meta $ substitute (asub u) a) ◁ τ)
    lem-A6 (mtc-tabs x) with lem-A6 x
    lem-A6 (mtc-tabs x) | t' // n ◅ u , p = u , m-tabs {!p!} 
    lem-A6 (mtc-iabs x) with lem-A6 x
    lem-A6 (mtc-iabs x) | u , p = u , (m-iabs p)
    lem-A6 {τ = τ} (mtc-simp {a = a} (u , eq)) =
      u , subst (flip _◁_ τ) (sym $ mgu-unifies (simpl a) τ (u , eq)) m-simp

    lem-A6' : ∀ {ν} {ρs} {r : Type ν} {a} → r ◁ a → ρs ⊢ (to-meta {zero} r) amatch a
    lem-A6' {a = a} m-simp = mtc-simp (mgu-id a) 
    lem-A6' (m-tabs r◁a) = mtc-tabs {!!}
    lem-A6' (m-iabs r◁a) = mtc-iabs (lem-A6' r◁a)

    -- p'haps counterintuitively the following proposition is NOT a theorem:
    -- Δ⊢ᵣa⟶Δ≢Ø : ∀ {ν n} {K : Ktx ν n} {a} → K ⊢ᵣ a → ∃ λ b → b List.∈ (proj₂ K)
    -- since [] ⊢ᵣ Nat ⇒ Nat through the r-iabs rule, but also:
    -- [] ⊢ᵣ Nat ⇒ (Nat ⇒ Nat), etc; through recursion on r-iabs

    lem-A7a : ∀ {ν} (Δ : ICtx ν) {a} → Δ ⊢match1st a → ∃ λ r → Δ ⟨ a ⟩= r
    lem-A7a List.[] ()
    lem-A7a (x List.∷ Δ) {a = a} (m1-head x₁) = , (l-head u Δ)
        where
        p = lem-A6 x₁
        u = subst (λ u' → u' ◁ a) (alist-zero-vanishes (proj₁ p)) (proj₂ p)
    lem-A7a (r List.∷ Δ) (m1-tail ¬pr y) =
        , (l-tail (λ r◁a → ¬pr $ lem-A6' r◁a) (proj₂ $ lem-A7a Δ y))

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
