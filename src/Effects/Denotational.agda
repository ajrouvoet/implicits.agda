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


⟦_,_⟧e : ∀ {ν η} → E.Effect η → TCtx ν η → C.Type (ν N+ η)
⟦ evar x , m ⟧e = tvar (lookup-evar m x)
⟦ has read , m ⟧e = tc CanRead
⟦ has write , m ⟧e = tc CanWrite
⟦ has throw , m ⟧e = tc CanThrow
⟦ has io , m ⟧e = tc CanIO
⟦_,_⟧e {ν} {η} (H x) m  = ∀' (subst C.Type (+-suc ν η) (⟦ x , m +evar ⟧e))

⟦_,_⟧efs : ∀ {ν η} → E.Effects η → TCtx ν η → C.Type (ν N+ η)
⟦ List.[] , m ⟧efs = C.tc unit
⟦ e List.∷ List.[] , m ⟧efs = ⟦ e , m ⟧e
⟦ e List.∷ d List.∷ ef , m ⟧efs = C.rec (fromList (List.map (λ e → ⟦ e , m ⟧e) ef))
  -- effects can be combined using the record type constructor

⟦_,_⟧tp : ∀ {ν η} → E.Type ν η → TCtx ν η → C.Type (ν N+ η)
⟦ unit , m ⟧tp = tc unit
⟦ tvar x , m ⟧tp = C.tvar (lookup-tvar m x)
⟦ (a →[ e ] b ) , m ⟧tp = ⟦ a , m ⟧tp C.→' ⟦ b , m ⟧tp -- ((⟦ e , m ⟧efs) C.⇒ 
⟦ ∀' t , m ⟧tp = C.∀' ⟦ t , m +tvar ⟧tp
⟦_,_⟧tp {ν} {η} (H t) m = C.∀' (subst C.Type (+-suc ν η) ⟦ t , m +evar ⟧tp)

⟦_,_⟧ctx : ∀ {ν η n} → E.Ctx ν η n → TCtx ν η → C.Ktx (ν N+ η) n
⟦ C , m ⟧ctx = map (flip ⟦_,_⟧tp m) C , List.[]

infixl 8 ⟦_+_,_⟧tpef
⟦_+_,_⟧tpef : ∀ {ν η} → E.Type ν η → E.Effects η → TCtx ν η → C.Type (ν N+ η)
⟦ a + List.[] , m ⟧tpef = ⟦ a , m ⟧tp
⟦ a + e List.∷ List.[] , m ⟧tpef = ⟦ e , m ⟧e ⇒ ⟦ a , m ⟧tp
⟦ a + e List.∷ d List.∷ es , m ⟧tpef = ⟦ e & es , m ⟧efs ⇒ ⟦ a , m ⟧tp

-- type driven translation of effect terms into
-- terms from the implicit calculus
⟦_,_⟧ : ∀ {ν η n} {Γ : E.Ctx ν η n} {t a e} → Γ E.⊢ t ∈ a + e → TCtx ν η → C.Term (ν N+ η) n
⟦ does c , m ⟧ = C.ρ ⟦ has c , m ⟧e (C.new unit)
⟦ tt , m ⟧ = C.new unit
⟦ var x , m ⟧ = C.var x
⟦ λ' {e = List.[]} a wt , m ⟧ =
  C.λ' ⟦ a , m ⟧tp ⟦ wt , m ⟧
⟦ λ' {e = e List.∷ List.[]} a wt , m ⟧ =
  C.ρ ⟦ e , m ⟧e (C.λ' ⟦ a , m ⟧tp (tmtm-weaken ⟦ wt , m ⟧))
⟦ λ' {e = e List.∷ d List.∷ es} a wt , m ⟧ =
  C.ρ ⟦ e & d & es , m ⟧efs (C.λ' ⟦ a , m ⟧tp (tmtm-weaken ⟦ wt , m ⟧))
⟦ wt₁ · wt₂ , m ⟧ = ⟦ wt₁ , m ⟧ C.· ⟦ wt₂ , m ⟧
⟦ Λ wt , m ⟧ = C.Λ ⟦ wt , m +tvar ⟧
⟦ wt [ b ] , m ⟧ = ⟦ wt , m ⟧ C.[ ⟦ b , m ⟧tp ]
⟦_,_⟧ {ν} {η} {n} (H wt) m = C.Λ (subst (flip C.Term n) (+-suc ν η) ⟦ wt , m +evar ⟧)
⟦ wt ! f , m ⟧ = ⟦ wt , m ⟧ C.[ ⟦ f , m ⟧efs ]

module Lemmas where
  -- lookup in and interpreted context Γ is equivalent to interpreting a type, looked up in K
  lookup⋆⟦⟧ctx : ∀ {ν η n} (C : Ctx ν η n) (m : TCtx ν η) x →
                 lookup x (proj₁ ⟦ C , m ⟧ctx) ≡ ⟦ lookup x C , m ⟧tp
  lookup⋆⟦⟧ctx C m x = sym $ lookup⋆map C (flip ⟦_,_⟧tp m) x 

open Lemmas

⟦⟧-preserves : ∀ {ν η n} {Γ : E.Ctx ν η n} {t a e} →
  (wt : Γ E.⊢ t ∈ a + e) → (m : TCtx ν η) → ⟦ Γ , m ⟧ctx C.⊢ ⟦ wt , m ⟧ ∈ ⟦ a + e , m ⟧tpef
⟦⟧-preserves {Γ = Γ} (var x) m =
  subst (λ u → _ C.⊢ C.var x ∈ u) (lookup⋆⟦⟧ctx Γ m x) (C.var x)
⟦⟧-preserves (λ' {e = List.[]} a wt) m = C.λ' ⟦ a , m ⟧tp (⟦⟧-preserves wt m)
⟦⟧-preserves (λ' {e = e List.∷ List.[]} a wt) m = {!C.ρ ⟦ e , m ⟧e (C.λ' ⟦ a , m ⟧tp (⟦⟧-preserves wt m))!}
⟦⟧-preserves (λ' {e = e List.∷ d List.∷ es} a wt) m = {!!}
⟦⟧-preserves (wt · wt₁) m = {!!}
⟦⟧-preserves (Λ wt) m = {!!}
⟦⟧-preserves (wt [ b ]) m = {!!}
⟦⟧-preserves (H wt) m = {!!}
⟦⟧-preserves (wt ! f) m = {!!}
⟦⟧-preserves (does c) m = C.ρ ⟦ has c , m ⟧e (C.new unit)
⟦⟧-preserves tt m = C.new unit
