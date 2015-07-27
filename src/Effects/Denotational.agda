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

-- the type constants
data TC : Set where
  unit : TC
  
  CanRead : TC
  CanWrite : TC
  CanThrow : TC
  CanIO : TC

open import Effects.WellTyped as E

-- make all calculus stuff available in the C._ namespace
module C where
  open import Implicits.Calculus TC public
  open import Implicits.Calculus.Terms.Constructors TC public
    renaming (id to cid)

-- import the syntax of the calculus
open import Implicits.Calculus.Terms
open import Implicits.Calculus.Types

bootstrap-len : ℕ
bootstrap-len = 7

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

fst : ∀ {ν n} → C.Term ν n
fst = Λ (Λ (λ' (tvar (suc zero)) (λ' (tvar zero) (var (suc zero)))))

snd : ∀ {ν n} → C.Term ν n
snd = Λ (Λ (λ' (tvar (suc zero)) (λ' (tvar zero) (var zero))))

bootstrap : C.Term 0 bootstrap-len → C.Term 0 0
bootstrap t =
  let' fread in'
  let' fwrite in'
  let' fprint in'
  let' fthrow in'
  implicit pair in'
  implicit fst in'
  implicit snd in' 
    t

postulate tm-weaken⋆ : ∀ {ν n} k → C.Term ν n → C.Term ν (k N+ n)

⟦_,_⟧ef : ∀ {ν η} → E.Effect η → TCtx ν η → C.Type (ν N+ η)
⟦ evar x , m ⟧ef = tvar (lookup-evar m x)
⟦ IO , m ⟧ef = tc CanIO
⟦ Reads , m ⟧ef = tc CanRead
⟦ Writes , m ⟧ef = tc CanWrite
⟦ Throws , m ⟧ef = tc CanThrow
⟦ Pure , m ⟧ef = tc unit
⟦ x ∪ y , m ⟧ef = ⟦ x , m ⟧ef C.×' ⟦ y , m ⟧ef
⟦ H x , m ⟧ef = {!!} -- ∀' ⟦ x , m +evar ⟧ef

⟦_,_⟧tp : ∀ {ν η} → E.Type ν η → TCtx ν η → C.Type (ν N+ η)
⟦ unit , m ⟧tp = tc unit
⟦_,_⟧tp {η = η} (tvar x) m = C.tvar (lookup-tvar m x)
⟦_,_⟧tp {ν = ν} (a →[ e ] b ) m = ⟦ a , m ⟧tp C.→' ((⟦ e , m ⟧ef) C.⇒ ⟦ b , m ⟧tp)
⟦ ∀' t , m ⟧tp = C.∀' ⟦ t , m +tvar ⟧tp
⟦ H t , m ⟧tp = {!!} -- C.∀' ⟦ t , m +evar ⟧tp

-- type driven translation of effect terms into
-- terms from the implicit calculus
⟦_,_⟧ : ∀ {ν η n} {Γ : E.Ctx ν η n} {t a e} →
      Γ E.⊢ t ∈ a & e → TCtx ν η → C.Term (ν N+ η) (n N+ bootstrap-len)
⟦_,_⟧ {ν} {η} {n} read m = {!!}
⟦_,_⟧ {ν} {η} {n} write m = {!!}
⟦_,_⟧ {ν} {η} {n} throw m = {!!}
⟦_,_⟧ {ν} {η} {n} print m = {!!}
⟦ tt , m ⟧ = new unit
⟦ var x , m ⟧ = C.var (inject+ bootstrap-len x)
⟦ λ' a wt , m ⟧ =  C.λ' ⟦ a , m ⟧tp ⟦ wt , m ⟧
⟦ wt₁ · wt₂ , m ⟧ = ⟦ wt₁ , m ⟧ C.· ⟦ wt₂ , m ⟧
⟦ Λ wt , m ⟧ = C.Λ ⟦ wt , m +tvar ⟧
⟦ wt [ b ] , m ⟧ = ⟦ wt , m ⟧ C.[ ⟦ b , m ⟧tp ]
⟦ H wt , m ⟧ = {!!}
⟦ wt ! f , m ⟧ = {!!}

