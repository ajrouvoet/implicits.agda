open import Prelude hiding (All; module All; _>>=_; ⊥)

module Implicits.Improved.Finite2.PartialAlgorithm (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

open import Coinduction
open import Data.Fin.Substitution
open import Data.List.Any as Any
open import Data.List.All as All
open Membership-≡
open import Implicits.Oliveira.Types TC _tc≟_
open import Implicits.Oliveira.Terms TC _tc≟_
open import Implicits.Oliveira.Contexts TC _tc≟_
open import Implicits.Oliveira.Substitutions TC _tc≟_
open import Implicits.Oliveira.Substitutions.Lemmas TC _tc≟_
open import Implicits.Improved.Finite2.Resolution TC _tc≟_
open import Implicits.Oliveira.Types.Unification TC _tc≟_
open import Relation.Nullary.Decidable as Dec using () 
open import Function.Equivalence using (equivalence)

open import Category.Monad
open import Category.Functor
open import Category.Monad.Partiality as P

open P.Workaround

_?⊥P : ∀ (A : Set) → Set₁
A ?⊥P =  (Dec A) ⊥P

-- Resolution programs
ResP : ∀ {ν} → (ICtx ν) → Type ν → Set₁
ResP Δ r = (Δ ⊢ᵣ r) ?⊥P

-- Matching first programs
ResM1 : ∀ {ν} → (ICtx ν) → SimpleType ν → Set₁
ResM1 Δ τ = (∃ λ r → r List.∈ Δ × Δ ⊢ r ↓ τ) ?⊥P

-- Matching programs
ResM : ∀ {ν} → (ICtx ν) → Type ν → SimpleType ν → Set₁
ResM Δ r τ = (Δ ⊢ r ↓ τ) ?⊥P

module M = MetaTypeMetaSubst
module T = MetaTypeTypeSubst

module Lemmas where

  {-}
  lem₀ : ∀ {m ν} {u u' : Sub (flip MetaType ν) m zero} (b : MetaType zero ν) →
         ((u M.↑) M.⊙ (M.sub b)) ≡ ((u' M.↑) M.⊙ (M.sub b)) → u ≡ u'
  lem₀ p b = {!!}
  -}

  lem₁ : ∀ {m ν} {Δ : ICtx ν} (a : MetaType m ν) τ u u' →
                   Δ ⊢ (from-meta (a M./ u)) ↓ τ → Δ ⊢ (from-meta (a M./ u')) ↓ τ → u ≡ u'
  lem₁ (a ⇒ b) τ u u' (i-iabs x p) (i-iabs x' p') = lem₁ b τ u u' p p'
  lem₁ (∀' a) τ u u' (i-tabs b p) (i-tabs b₁ q) = {!!}
    -- lem₀ (to-meta b) (lem₁ {!a!} τ (u T.↑tp T.⊙ sub (to-meta b)) (u' ↑ ⊙ sub (to-meta b)) p q)
  lem₁ (simpl x) τ u u' p q = {!!}

  postulate lem₂ : ∀ {m ν} {Δ : ICtx ν} (x : MetaSimpleType m ν) {τ} u →
                   Δ ⊢ from-meta ((simpl x) M./ u) ↓ τ →
                   ∃ λ u → (from-meta ((simpl x) M./ u) ≡ simpl τ)

  {-}
  postulate lem₃ : ∀ {ν} (a : MetaType zero (suc ν)) (u : MetaType zero ν) →
                  (from-meta a) tp[/tp from-meta u ] ≡ from-meta ((open-meta a) M./ (M.sub u))
  lem (a ⇒ b) u = cong₂ _⇒_ (lem a u) (lem b u)
  lem (∀' a) u = begin
    ((from-meta (∀' a)) TypeSubst./ TypeSubst.sub (from-meta u))
      ≡⟨ refl ⟩
    ((∀' (from-meta a)) TypeSubst./ TypeSubst.sub (from-meta u))
      ≡⟨ {!!} ⟩
    (from-meta (((open-meta (∀' a)) / (sub u))))
      ≡⟨ {!!} ⟩
    (from-meta (((open-meta (∀' a)) / (sub u)))) ∎
  lem (simpl (tvar zero)) u = refl
  lem (simpl (tvar (suc x))) u = begin
    (from-meta (simpl (tvar (suc x)))) tp[/tp from-meta u ]
      ≡⟨ TypeLemmas.suc-/-sub {t = (from-meta u)}⟩
    (simpl (tvar x))
      ≡⟨ cong (λ v → from-meta (_/_ v (sub u))) (sym $ open-tvar-suc x) ⟩
    from-meta ((open-meta (simpl (tvar (suc x)))) / (sub u)) ∎
  lem (simpl (mvar ())) u
  lem (simpl (a →' b)) u = cong₂ (λ w v → simpl (w →' v)) (lem a u) (lem b u)
  lem (simpl (tc c)) u = refl
  -}
  
  postulate lem₄ : ∀ {m ν} (a : MetaType m (suc ν)) u us → from-meta ((M.open-meta a) M./ (us M.↑) M./ (M.sub u)) ≡ (from-meta (a M./ (us M.↑tp))) tp[/tp from-meta u ]
  -- lem' a u us = {!!}

open Lemmas

mutual
  private
    ResM' : ∀ {m ν} → (ICtx ν) → MetaType m ν → SimpleType ν → Set₁
    ResM' Δ r τ = (∃ λ u → Δ ⊢ from-meta (r M./ u) ↓ τ) ?⊥P

    -- match' uses MetaType m ν instead of Type ν to be able to distinguish unification variables
    -- from other, non-unifiable tvars.
    -- The difference is subtle but the gist is that we can only unify variables that we open
    -- during matching. Any variables that are already open in the context are fixed.
    match' : ∀ {ν m} (Δ : ICtx ν) → (τ : SimpleType ν) → (r' : MetaType m ν) → ResM' Δ r' τ 

    -- For rule types we first check if b matches our query τ.
    -- If this is the case, we use the unifier to instantiate the unification vars in a and
    -- recursively try to resolve the result.
    -- If that succeeds as well, we use i-iabs to return a result
    match' Δ τ (a ⇒ b) = later (♯ (match' Δ τ b >>= lem))
      where
        lem : Dec (∃ λ u → Δ ⊢ (from-meta (b M./ u)) ↓ τ) → ResM' Δ (a ⇒ b) τ
        lem (yes (u , b/u↓τ)) = resolve' Δ (from-meta (a M./ u)) >>= f
          where
            f : Dec (Δ ⊢ᵣ (from-meta (a M./ u))) →
                Dec (∃ (λ u → Δ ⊢ from-meta (a ⇒ b M./ u) ↓ τ)) ⊥P
            f (yes Δ⊢ᵣa) = now (yes (u , (i-iabs Δ⊢ᵣa b/u↓τ)))
            f (no ¬p)    =
              now (no (λ{ (u' , i-iabs x b/u↓τ') →
                ¬p (
                  subst
                    (λ v → Δ ⊢ᵣ from-meta (a M./ v))
                    (lem₁ b τ u' u b/u↓τ' b/u↓τ)
                    x)}))
        lem (no ¬p) = now (no (λ{ (_ , i-iabs x p) → ¬p (, p) }))

    -- On type vars we simply open it up, adding the tvar to the set of unification variables.
    -- and recursively try to match.
    -- If matching succeeds, we can use i-tabs to return a result
    -- This needs to be wrapped in a 'later' because Agda doesn't see that open-meta a
    -- is structurally smaller than (∀' a)
    match' Δ τ (∀' a) = later (♯ ((match' Δ τ (open-meta a)) >>= (
        λ x → now (Dec.map (equivalence lem lem′) x)
      )))
      where
        open MetaTypeMetaLemmas hiding (subst)

        eq : ∀ u us a → from-meta ((open-meta a) M./ (u ∷ us)) ≡
          (from-meta (a M./ (us M.↑tp))) tp[/tp from-meta u ]
        eq u us a = begin
          from-meta (M._/_ (open-meta a) (u ∷ us))
            ≡⟨ cong (λ v → from-meta (M._/_ (open-meta a) v)) (sym $ us↑-⊙-sub-u≡u∷us u us) ⟩
          from-meta ((open-meta a) M./ (us M.↑ M.⊙ (M.sub u)))
            ≡⟨ cong from-meta (/-⊙ (open-meta a)) ⟩
          from-meta ((open-meta a) M./ us M.↑ M./ (M.sub u))
            ≡⟨ lem₄ a u us ⟩
          from-meta (M._/_ a (us M.↑tp)) tp[/tp from-meta u ] ∎

        lem : (∃ λ u → Δ ⊢ (from-meta ((open-meta a) M./ u)) ↓ τ) →
              ∃ λ u' → Δ ⊢ (from-meta (∀' a M./ u')) ↓ τ
        lem (u ∷ us , p) = us , (i-tabs (from-meta u) (subst (λ v → Δ ⊢ v ↓ τ) (eq u us a) p))

        lem′ : (∃ λ u' → Δ ⊢ (from-meta (∀' a M./ u')) ↓ τ) →
               ∃ λ u → Δ ⊢ (from-meta ((open-meta a) M./ u)) ↓ τ
        lem′ (proj₁ , i-tabs b proj₂) = {!!}

    -- The only thing left to do is to try and unify τ and x.
    -- If we succeed, we use  i-simpl to return a result.
    match' Δ τ (simpl x) with mgu (simpl x) τ | inspect (mgu (simpl x)) τ
    match' Δ τ (simpl x) | just (u , p) | _ =
      now (yes (
        asub u ,
        subst (λ a → Δ ⊢ a ↓ τ) (sym $ mgu-unifies (simpl x) τ (u , p)) (i-simp τ)
      ))
    match' Δ τ (simpl x) | nothing | reveal[ eq ] = now (no (
      λ{ (u , x/u↓τ) → mgu-sound' (simpl x) τ eq (lem₂ x u x/u↓τ)}))

  -- match defers to match', which concerns itself with MetaTypes.
  -- If match' finds a match, we can use the fact that we have zero unification variables open here
  -- to show that we found the right thing.
  match : ∀ {ν} (Δ : ICtx ν) → (r : Type ν) → (τ : SimpleType ν) → ResM Δ r τ 
  match Δ a τ = (match' Δ τ (to-meta {zero} a)) >>= (λ x → now (Dec.map (equivalence lem lem′) x))
    where
      eq : ∀ {ν} {a : Type ν} {s} → from-meta (to-meta {zero} a M./ s) ≡ a
      eq {a = a} {s = []} = begin
        from-meta (M._/_ (to-meta {zero} a) [])
          ≡⟨ cong (λ q → from-meta q) (MetaTypeMetaLemmas.id-vanishes (to-meta {zero} a)) ⟩
        from-meta (to-meta {zero} a)
          ≡⟨ to-meta-zero-vanishes ⟩
        a ∎
      lem : ∃ (λ u → Δ ⊢ from-meta (to-meta {zero} a M./ u) ↓ τ) → Δ ⊢ a ↓ τ
      lem ([] , a/u↓τ) = subst (λ u → Δ ⊢ u ↓ τ) eq a/u↓τ
      lem′ : Δ ⊢ a ↓ τ → ∃ λ u → Δ ⊢ from-meta (to-meta {zero} a M./ u) ↓ τ
      lem′ a↓τ = [] , subst (λ u → Δ ⊢ u ↓ τ) (sym eq) a↓τ
        

  match1st : ∀ {ν} {Δ : ICtx ν} → (ρs : ICtx ν) →
             ρs ⊆ Δ → (τ : SimpleType ν) →
             All (λ x → x List.∈ ρs ⊎ (¬ Δ ⊢ x ↓ τ)) Δ → 
             ResM1 Δ τ
  match1st {Δ = Δ} List.[] ρs⊆Δ τ p = now (no lem)
    where
      lem : ¬ ∃ λ r → r List.∈ Δ × Δ ⊢ r ↓ τ
      lem (r , r∈Δ , r↓τ) with All.lookup p r∈Δ 
      lem (r , r∈Δ , r↓τ) | inj₁ ()
      lem (r , r∈Δ , r↓τ) | inj₂ y = y r↓τ
  match1st {Δ = Δ} (x List.∷ ρs) ρs⊆Δ τ p = match Δ x τ >>= recoverOnFail
    where
      recoverOnFail : Dec (Δ ⊢ x ↓ τ) → ResM1 Δ τ
      recoverOnFail (yes r↓a) = now (yes (x , (ρs⊆Δ (here refl) , r↓a)))
      recoverOnFail (no ¬p) = match1st ρs (λ y → ρs⊆Δ (there y)) τ (All.map lem p)
        where
          lem : ∀ {y} → y List.∈ (x List.∷ ρs) ⊎ (¬ Δ ⊢ y ↓ τ) → y List.∈ ρs ⊎ (¬ Δ ⊢ y ↓ τ)
          lem {y} (inj₁ p) with y ≟ x
          lem (inj₁ p₂) | yes refl = inj₂ ¬p
          lem (inj₁ p₁) | no ¬p₁ = inj₁ (Any.tail ¬p₁ p₁)
          lem (inj₂ x) = inj₂ x

  -- resolution in ResP
  resolve' : ∀ {ν} (Δ : ICtx ν) (a : Type ν) → ResP Δ a
  resolve' Δ (simpl x) = match1st {Δ = Δ} Δ id x (All.tabulate inj₁) >>= (
      λ v → now (Dec.map (equivalence
        (λ { (r , r∈Δ , r↓x) → r-simp r∈Δ r↓x })
        (λ { (r-simp r∈Δ r↓τ) → , (r∈Δ , r↓τ) })) v))
  resolve' Δ (a ⇒ b) = resolve' (a List.∷ Δ) b >>= (
      λ v → now (Dec.map (equivalence (λ{ x → r-iabs x}) (λ{ (r-iabs x) → x })) v))
  resolve' Δ (∀' a) = resolve' (ictx-weaken Δ) a >>= (
      λ v → now (Dec.map (equivalence (λ x → r-tabs x) (λ{ (r-tabs x) → x})) v))

  resolve : ∀ {ν} (Δ : ICtx ν) (r : Type ν) → (Dec (Δ ⊢ᵣ r)) ⊥
  resolve Δ r = ⟦ resolve' Δ r ⟧P

  _resolved? : ∀ {ν} {Δ : ICtx ν} {r : Type ν} → (Dec (Δ ⊢ᵣ r)) ⊥ → Bool
  now (yes x) resolved? = true
  now (no ¬p) resolved? = false
  later x resolved? = false

  _failed? : ∀ {ν} {Δ : ICtx ν} {r : Type ν} → (Dec (Δ ⊢ᵣ r)) ⊥ → Bool
  now (yes x) failed? = false
  now (no ¬p) failed? = true
  later x failed? = false

  _resolves_after_steps : ∀ {ν} (Δ : ICtx ν) (r : Type ν) → ℕ → Bool
  Δ resolves r after n steps = (run_for_steps (resolve Δ r) n) resolved?
