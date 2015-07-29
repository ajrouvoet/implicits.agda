module Implicits.SystemF.Terms.Constructors (TC : Set) where

open import Prelude
open import Implicits.SystemF.WellTyped TC
open import Implicits.SystemF.Substitutions.Lemmas TC
open import Implicits.SystemF.Substitutions TC
open import Implicits.SystemF.Types.Constructors TC

-- polymorphic function application
-- applies a polymorphic function to an argument with the type of the domain
poly-· : ∀ {ν n} {a : Type ν} {K : Ctx ν n} {f arg} →
         (fa : IsFunction a) → K ⊢ f ∈ a → K ⊢ arg ∈ domain fa → ∃ λ t → K ⊢ t ∈ codomain fa
poly-· (lambda a b) ⊢f ⊢arg = , ⊢f · ⊢arg
poly-· {K = K} {f = f} {arg = arg} (∀'-lambda {a} fa) ⊢f ⊢arg = , Λ (proj₂ (poly-· fa f' arg'))
  where
    f' : ctx-weaken K ⊢ _ ∈ a
    f' = subst
      (λ τ → ctx-weaken K ⊢ _ ∈ τ)
     (TypeLemmas.a-/Var-varwk↑-/-sub0≡a a)
      ((⊢tp-weaken ⊢f) [ tvar zero ])
    arg' : ctx-weaken K ⊢ (tm-weaken arg) [ tvar zero ] ∈ domain fa
    arg' = subst
      (λ τ → ctx-weaken K ⊢ _ ∈ τ)
      (TypeLemmas.a-/Var-varwk↑-/-sub0≡a (domain fa))
      ((⊢tp-weaken ⊢arg) [ tvar zero ])

-- Polymorphic identity function
id' : {ν n : ℕ} → Term ν n
id' = Λ (λ' (tvar zero) (var zero))

-- Bottom elimination/univeral property of the initial type
⊥-elim : ∀ {m n} → Type n → Term n m
⊥-elim a = λ' ⊥' ((var zero) [ a ])

-- Unit value
tt = id'

-- n-ary term abstraction
λⁿ : ∀ {ν m k} → Vec (Type ν) k → Term ν (k N+ m) → Term ν m
λⁿ []       t = t
λⁿ (a ∷ as) t = λⁿ as (λ' a t)

infixl 9 _·ⁿ_

-- n-ary term application
_·ⁿ_ : ∀ {m n k} → Term m n → Vec (Term m n) k → Term m n
s ·ⁿ []       = s
s ·ⁿ (t ∷ ts) = (s ·ⁿ ts) · t

-- Record/tuple constructor
newrec : ∀ {ν n k} → Vec (Term ν n) k → {as : Vec (Type ν) k} → Term ν n
newrec []                = tt
newrec (t ∷ ts) {a ∷ as} =
  Λ (λ' (map tp-weaken (a ∷ as) →ⁿ tvar zero)
    (var zero ·ⁿ map tmtm-weaken (map tm-weaken (t ∷ ts))))

-- Field access/projection
π : ∀ {ν n k} → Fin k → Term ν n → {as : Vec (Type ν) k} → Term ν n
π     () t {[]}
π {n = n} x  t {as} =
  (t [ lookup x as ]) · (λⁿ as (var (inject+ n x)))
