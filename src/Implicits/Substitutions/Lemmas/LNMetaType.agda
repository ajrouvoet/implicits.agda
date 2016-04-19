open import Prelude renaming (lift to finlift) hiding (id; subst)

module Implicits.Substitutions.Lemmas.LNMetaType where

open import Implicits.Syntax.LNMetaType
open import Implicits.Substitutions.LNMetaType

open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas 
open import Data.Vec.Properties
open import Data.Star using (Star; ε; _◅_)
open import Data.Nat.Properties
open import Data.Nat as Nat
open import Extensions.Substitution
open import Relation.Binary using (module DecTotalOrder)
open DecTotalOrder decTotalOrder using () renaming (refl to ≤-refl; trans to ≤-trans)
open import Relation.Binary.HeterogeneousEquality as H using ()
module HR = H.≅-Reasoning

typeLemmas : TermLemmas MetaType
typeLemmas = record { termSubst = typeSubst; app-var = refl ; /✶-↑✶ = Lemma./✶-↑✶ }
  where
    module Lemma {T₁ T₂} {lift₁ : Lift T₁ MetaType} {lift₂ : Lift T₂ MetaType} where

      open Lifted lift₁ using () renaming (_↑✶_ to _↑✶₁_; _/✶_ to _/✶₁_)
      open Lifted lift₂ using () renaming (_↑✶_ to _↑✶₂_; _/✶_ to _/✶₂_)

      /✶-↑✶ : ∀ {m n} (σs₁ : Subs T₁ m n) (σs₂ : Subs T₂ m n) → 
                          (∀ k x → (simpl (mvar x)) /✶₁ σs₁ ↑✶₁ k ≡ (simpl (mvar x)) /✶₂ σs₂ ↑✶₂ k) → 
                          ∀ k t → t /✶₁ σs₁ ↑✶₁ k ≡ t /✶₂ σs₂ ↑✶₂ k
      /✶-↑✶ ρs₁ ρs₂ hyp k (simpl (mvar x)) = hyp k x
      /✶-↑✶ ρs₁ ρs₂ hyp k (simpl (tvar x)) = begin
          simpl (tvar x) /✶₁ ρs₁ ↑✶₁ k
          ≡⟨ MetaTypeApp.tvar-/✶-↑✶ _ k ρs₁ ⟩
          simpl (tvar x)
          ≡⟨ sym $ MetaTypeApp.tvar-/✶-↑✶ _ k ρs₂ ⟩
          simpl (tvar x) /✶₂ ρs₂ ↑✶₂ k ∎
      /✶-↑✶ ρs₁ ρs₂ hyp k (simpl (tc c)) = begin
          (simpl (tc c)) /✶₁ ρs₁ ↑✶₁ k
          ≡⟨ MetaTypeApp.tc-/✶-↑✶ _ k ρs₁ ⟩
          (simpl (tc c))
          ≡⟨ sym $ MetaTypeApp.tc-/✶-↑✶ _ k ρs₂ ⟩
          (simpl (tc c)) /✶₂ ρs₂ ↑✶₂ k ∎
      /✶-↑✶ ρs₁ ρs₂ hyp k (simpl (a →' b)) = begin
          (simpl (a →' b)) /✶₁ ρs₁ ↑✶₁ k
          ≡⟨ MetaTypeApp.→'-/✶-↑✶ _ k ρs₁ ⟩
          simpl ((a /✶₁ ρs₁ ↑✶₁ k) →' (b /✶₁ ρs₁ ↑✶₁ k))
          ≡⟨ cong₂ (λ a b → simpl (a →' b)) (/✶-↑✶ ρs₁ ρs₂ hyp k a) (/✶-↑✶ ρs₁ ρs₂ hyp k b) ⟩
          simpl ((a /✶₂ ρs₂ ↑✶₂ k) →' (b /✶₂ ρs₂ ↑✶₂ k))
          ≡⟨ sym (MetaTypeApp.→'-/✶-↑✶ _ k ρs₂) ⟩
          (simpl (a →' b)) /✶₂ ρs₂ ↑✶₂ k
          ∎
      /✶-↑✶ ρs₁ ρs₂ hyp k (a ⇒ b) = begin
          (a ⇒ b) /✶₁ ρs₁ ↑✶₁ k
          ≡⟨ MetaTypeApp.⇒-/✶-↑✶ _ k ρs₁ ⟩ -- 
          (a /✶₁ ρs₁ ↑✶₁ k) ⇒ (b /✶₁ ρs₁ ↑✶₁ k)
          ≡⟨ cong₂ _⇒_ (/✶-↑✶ ρs₁ ρs₂ hyp k a) (/✶-↑✶ ρs₁ ρs₂ hyp k b) ⟩
          (a /✶₂ ρs₂ ↑✶₂ k) ⇒ (b /✶₂ ρs₂ ↑✶₂ k)
          ≡⟨ sym (MetaTypeApp.⇒-/✶-↑✶ _ k ρs₂) ⟩
          (a ⇒ b) /✶₂ ρs₂ ↑✶₂ k
          ∎
      /✶-↑✶ ρs₁ ρs₂ hyp k (∀' a) = begin
          (∀' a) /✶₁ ρs₁ ↑✶₁ k
          ≡⟨ MetaTypeApp.∀'-/✶-↑✶ _ k ρs₁ ⟩
          ∀' (a /✶₁ ρs₁ ↑✶₁ k)
          ≡⟨ cong ∀' (/✶-↑✶ ρs₁ ρs₂ hyp k a) ⟩
          ∀' (a /✶₂ ρs₂ ↑✶₂ k)
          ≡⟨ sym (MetaTypeApp.∀'-/✶-↑✶ _ k ρs₂) ⟩
          (∀' a) /✶₂ ρs₂ ↑✶₂ k
          ∎

open TermLemmas typeLemmas public hiding (var; id; _/_; _↑⋆_; wk; weaken; sub)
open AdditionalLemmas typeLemmas public

-- The above lemma /✶-↑✶ specialized to single substitutions
/-↑⋆ : ∀ {T₁ T₂} {lift₁ : Lift T₁ MetaType} {lift₂ : Lift T₂ MetaType} →
    let open Lifted lift₁ using () renaming (_↑⋆_ to _↑⋆₁_; _/_ to _/₁_)
        open Lifted lift₂ using () renaming (_↑⋆_ to _↑⋆₂_; _/_ to _/₂_)
    in
    ∀ {n k} (ρ₁ : Sub T₁ n k) (ρ₂ : Sub T₂ n k) →
    (∀ i x → (simpl (mvar x)) /₁ ρ₁ ↑⋆₁ i ≡ (simpl (mvar x)) /₂ ρ₂ ↑⋆₂ i) →
        ∀ i a → a /₁ ρ₁ ↑⋆₁ i ≡ a /₂ ρ₂ ↑⋆₂ i
/-↑⋆ ρ₁ ρ₂ hyp i a = /✶-↑✶ (ρ₁ ◅ ε) (ρ₂ ◅ ε) hyp i a

-- weakening a simple type gives a simple type
simpl-wk : ∀ {ν} k (τ : MetaSType (k N+ ν)) → ∃ λ τ' → (simpl τ) / wk ↑⋆ k ≡ simpl τ'
simpl-wk k (tc x) = , refl
simpl-wk k (mvar n) = , var-/-wk-↑⋆ k n
simpl-wk k (tvar n) = , refl
simpl-wk k (x →' x₁) = , refl

tclosed-wk : ∀ {ν m} {a : MetaType m} → TClosed ν a → TClosed (suc ν) a
tclosed-wk (a ⇒ b) = tclosed-wk a ⇒ tclosed-wk b
tclosed-wk (∀' x) = ∀' (tclosed-wk x)
tclosed-wk (simpl x) = simpl $ tclosed-wks x
  where
    tclosed-wks : ∀ {ν m} {τ : MetaSType m} → TClosedS ν τ → TClosedS (suc ν) τ
    tclosed-wks (tvar p) = tvar (≤-steps 1 p)
    tclosed-wks mvar = mvar
    tclosed-wks (a →' b) = (tclosed-wk a) →' (tclosed-wk b)
    tclosed-wks tc = tc

-- proper substitution doesn't affect the number of tvars
tclosed-/ : ∀ {m m' n} (a : MetaType m) {σ : Sub MetaType m m'} → TClosed n a →
            (∀ i → TClosed n (lookup i σ)) → TClosed n (a / σ)
tclosed-/ (a ⇒ b) (ca ⇒ cb) f = tclosed-/ a ca f ⇒ tclosed-/ b cb f
tclosed-/ (∀' a) (∀' x) f = ∀' (tclosed-/ a x (λ p → tclosed-wk (f p)))
tclosed-/ (simpl x) (simpl y) f = tclosed-/s x y f
  where
    tclosed-/s : ∀ {m m' n} (a : MetaSType m) {σ : Sub MetaType m m'} → TClosedS n a →
                 (∀ i → TClosed n (lookup i σ)) → TClosed n (a simple/ σ)
    tclosed-/s (tvar _) (tvar p) f = simpl (tvar p)
    tclosed-/s (mvar i) _ f = f i
    tclosed-/s (a →' b) (ca →' cb) f = simpl (tclosed-/ a ca f →' tclosed-/ b cb f)
    tclosed-/s (tc c) _ _ = simpl tc

-- opening any free tvar will reduce the number of free tvars
tclosed-open : ∀ {m ν} {a : MetaType m} k → k N< (suc ν) → TClosed (suc ν) a →
               TClosed ν (open-meta k a)
tclosed-open k k<ν (a ⇒ b) = (tclosed-open k k<ν a) ⇒ (tclosed-open k k<ν b)
tclosed-open k k<ν (∀' a) = ∀' (tclosed-open (suc k) (s≤s k<ν) a)
tclosed-open k k<ν (simpl (tvar {x = x} p)) with Nat.compare x k
tclosed-open .(suc (k' N+ k)) (s≤s k<ν) (simpl (tvar p)) | less k' k =
  simpl (tvar (≤-trans (m≤m+n (suc k') k) k<ν))
tclosed-open x k<ν (simpl (tvar x₁)) | equal .x = simpl mvar
tclosed-open m k<ν (simpl (tvar (s≤s p))) | greater .m k = simpl (tvar p)
tclosed-open k k<ν (simpl mvar) = simpl mvar
tclosed-open k k<ν (simpl (x →' x₁)) = simpl (tclosed-open k k<ν x →' tclosed-open k k<ν x₁)
tclosed-open k k<ν (simpl tc) = simpl tc

open-meta-◁m₁ : ∀ {m k} (a : MetaType m) → (open-meta k a) ◁m₁ ≡ a ◁m₁
open-meta-◁m₁ (a ⇒ b) = open-meta-◁m₁ b
open-meta-◁m₁ (∀' a) = cong suc (open-meta-◁m₁ a)
open-meta-◁m₁ (simpl x) = refl

lem : ∀ {m} n k (a : MetaType m) → open-meta n (open-meta (n N+ suc k) a) H.≅
                                    open-meta (n N+ k) (open-meta n a)
lem n k (a ⇒ b) = H.cong₂ _⇒_ (lem n k a) (lem n k b)
lem n k (∀' a) = H.cong ∀' (lem _ _ a)
lem n k (simpl (tvar x)) with Nat.compare x (n N+ (suc k))
lem n k (simpl (tvar x)) | z = {!z!}
lem n k (simpl (mvar x)) = H.refl
lem n k (simpl (a →' b)) = H.cong₂ (λ u v → simpl (u →' v)) (lem n k a) (lem n k b)
lem n k (simpl (tc x)) = H.refl

open-meta-◁m : ∀ {m} k (a : MetaType m) →
               ((open-meta k a) ◁m) H.≅ open-meta k (a ◁m)
open-meta-◁m k (a ⇒ b) = open-meta-◁m k b
open-meta-◁m k (∀' a) = HR.begin
  open-meta zero ((open-meta (suc k)) a ◁m)
    HR.≅⟨  {!!} ⟩
  open-meta zero (open-meta (suc k) (a ◁m))
    HR.≅⟨ lem zero k (a ◁m) ⟩
  open-meta k (open-meta zero (a ◁m)) HR.∎
open-meta-◁m k (simpl x) = H.refl

open import Implicits.Syntax.Type
open import Implicits.Substitutions.Type as TS using ()

lem₁ : ∀ {ν} k (a : Type (k N+ suc ν)) (b : Type ν) →
                (to-meta (a TS./ (TS.sub b) TS.↑⋆ k)) ≡
                  (open-meta k (to-meta a) / sub (to-meta b))
lem₁ k (simpl (tc x)) b = refl
lem₁ k (simpl (tvar n)) b with Nat.compare (toℕ n) k
lem₁ k (simpl (tvar n)) b | z = {!!}
lem₁ k (simpl (a →' b)) c = cong₂ (λ u v → simpl (u →' v)) (lem₁ k a c) (lem₁ k b c)
lem₁ k (a ⇒ b) c = cong₂ _⇒_ (lem₁ k a c) (lem₁ k b c)
lem₁ k (∀' a) b = cong ∀' (lem₁ (suc k) a b)
