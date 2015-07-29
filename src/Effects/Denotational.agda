module Effects.Denotational where

open import Prelude
open import Data.Nat.Properties.Simple

-- translation context helps keep track of relation between
-- the domain's tvar/evars and the target language's tvars
TCtx : ℕ → ℕ → Set
TCtx ν η = Vec (Fin (ν N+ η)) ν × Vec (Fin (ν N+ η)) η

-- update the translation context when one
-- brings another tvar in scope
_+tvar : ∀ {ν η} → TCtx ν η → TCtx (suc ν) η
_+tvar {ν} {η} (tvars , evars) = 
  (fromℕ (ν N+ η)) ∷ map (λ x → (inject₁ x)) tvars ,
  map inject₁ evars

-- update the translation context when one
-- brings another evar in scope
_+evar : ∀ {ν η} → TCtx ν η → TCtx ν (suc η)
_+evar {ν} {η} (tvars , evars) =
  map (λ x → subst-comm (inject₁ x)) tvars ,
  (subst-comm (fromℕ (ν N+ η)) ∷ map (λ x → subst-comm (inject₁ x)) evars)
  where
    subst-comm = subst Fin (sym $ +-suc ν η) 

-- lookup the index of the resulting tvar given the index of an evar in the semantic domain
lookup-evar : ∀ {ν η} → TCtx ν η → Fin η → Fin (ν N+ η)
lookup-evar (_ , evars) x = lookup x evars

-- lookup the index of the resulting tvar given the index of a tvar in the semantic domain
lookup-tvar : ∀ {ν η} → TCtx ν η → Fin ν → Fin (ν N+ η)
lookup-tvar (tvars , _) x = lookup x tvars

-- the effect primitives
data EC : Set where
  read : EC
  write : EC
  throw : EC
  io : EC

_ec≟_ : Decidable {A = EC} _≡_
read ec≟ read = yes refl
read ec≟ write = no (λ ())
read ec≟ throw = no (λ ())
read ec≟ io = no (λ ())
write ec≟ read = no (λ ())
write ec≟ write = yes refl
write ec≟ throw = no (λ ())
write ec≟ io = no (λ ())
throw ec≟ read = no (λ ())
throw ec≟ write = no (λ ())
throw ec≟ throw = yes refl
throw ec≟ io = no (λ ())
io ec≟ read = no (λ ())
io ec≟ write = no (λ ())
io ec≟ throw = no (λ ())
io ec≟ io = yes refl

-- the type primitives
data TC : Set where
  unit : TC
  
  CanRead : TC
  CanWrite : TC
  CanThrow : TC
  CanIO : TC

open import Effects.WellTyped EC _ec≟_ as E
open import Effects.Substitutions EC _ec≟_ 

-- make all calculus stuff available in the C._ namespace
module C where
  open import Implicits.Calculus TC public
  open import Implicits.Calculus.Terms.Constructors TC public
    renaming (id to cid)

-- import the syntax of the calculus
open import Implicits.Calculus.Terms TC
open import Implicits.Calculus.Types TC
open import Implicits.Calculus.Substitutions TC

fread : ∀ {ν n} → C.Term ν n
fread = (ρ (tc CanRead) (new unit))

fwrite : ∀ {ν n} → C.Term ν n
fwrite = (ρ (tc CanWrite) (new unit))

fprint : ∀ {ν n} → C.Term ν n
fprint = (ρ (tc CanIO) (new unit))

fthrow : ∀ {ν n} → C.Term ν n
fthrow = (ρ (tc CanThrow) (new unit))

pair : ∀ {ν n} → C.Term ν n
pair =
  (Λ (Λ (
    -- 1st arg
    λ' (tvar (suc zero))
      -- 2nd arg
      (λ' (tvar zero)
        -- projector
        (λ'
          (∀' (tvar (suc (suc zero)) →' tvar (suc zero) →' tvar zero))
          ((
            -- apply projector to fst type arg and fst arg
            ((var zero) [ tvar (suc zero) ] · (var (suc (suc zero))))
            -- apply result to snd type arg and snd arg
            [ tvar zero ]) · (var (suc zero))
          )
  -- grandpa's parens
  )))))

⟦_,_⟧ef : ∀ {ν η} → E.Effects η → TCtx ν η → C.Type (ν N+ η)
⟦_,_⟧ef {ν} {η} ef m = List.foldl (λ acc e → ⟦ e , m ⟧e C.×' acc) (C.tc unit) ef
  where
    ⟦_,_⟧e : ∀ {ν η} → E.Effect η → TCtx ν η → C.Type (ν N+ η)
    ⟦ evar x , m ⟧e = tvar (lookup-evar m x)
    ⟦ has read , m ⟧e = tc CanRead
    ⟦ has write , m ⟧e = tc CanWrite
    ⟦ has throw , m ⟧e = tc CanThrow
    ⟦ has io , m ⟧e = tc CanIO
    ⟦_,_⟧e {ν} {η} (H x) m  = ∀' (subst C.Type (+-suc ν η) (⟦ x , m +evar ⟧e))

⟦_,_⟧tp : ∀ {ν η} → E.Type ν η → TCtx ν η → C.Type (ν N+ η)
⟦ unit , m ⟧tp = tc unit
⟦_,_⟧tp {η = η} (tvar x) m = C.tvar (lookup-tvar m x)
⟦_,_⟧tp {ν = ν} (a →[ e ] b ) m = ⟦ a , m ⟧tp C.→' ((⟦ e , m ⟧ef) C.⇒ ⟦ b , m ⟧tp)
⟦ ∀' t , m ⟧tp = C.∀' ⟦ t , m +tvar ⟧tp
⟦_,_⟧tp {ν} {η} (H t) m  = C.∀' (subst C.Type (+-suc ν η) ⟦ t , m +evar ⟧tp)

{-
⟦_&_,_⟧tp : ∀ {ν η} → E.Type ν η → E.Effect η → TCtx ν η → C.Type (ν N+ η)
⟦ a & e , m ⟧tp = {!e!}

-- type driven translation of effect terms into
-- terms from the implicit calculus
⟦_,_⟧ : ∀ {ν η n} {Γ : E.Ctx ν η n} {t a e} → Γ E.⊢ t ∈ a & e → TCtx ν η → C.Term (ν N+ η) n
⟦ does read , m ⟧ = fread
⟦ does write , m ⟧ = fwrite
⟦ does throw , m ⟧ = fthrow
⟦ does io , m ⟧ = fprint
⟦ tt , m ⟧ = new unit
⟦ var x , m ⟧ = C.var x
⟦ λ' a wt , m ⟧ =  C.λ' ⟦ a , m ⟧tp ⟦ wt , m ⟧
⟦ wt₁ · wt₂ , m ⟧ = ⟦ wt₁ , m ⟧ C.· ⟦ wt₂ , m ⟧
⟦ Λ wt , m ⟧ = C.Λ ⟦ wt , m +tvar ⟧
⟦ wt [ b ] , m ⟧ = ⟦ wt , m ⟧ C.[ ⟦ b , m ⟧tp ]
⟦_,_⟧ {ν} {η} {n} (H wt) m = C.Λ (subst (flip C.Term n) (+-suc ν η) ⟦ wt , m +evar ⟧)
⟦ wt ! f , m ⟧ = ⟦ wt , m ⟧ C.[ ⟦ f , m ⟧ef ]

{-
⟦⟧-preserves : ∀ {ν η n} {Γ : E.Ctx ν η n} {t a e} →
  (wt : Γ E.⊢ t ∈ a & e) → TCtx ν η → 
  ⟦ Γ ⟧ctx C.⊢ ⟦ wt , m ⟧ ∈ ⟦ a & e ⟧
  -}

-}
