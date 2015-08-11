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
  open import Implicits.Calculus.Substitutions TC
  open import Implicits.Calculus.Terms.Constructors TC public
    renaming (id to cid)
  open import Implicits.Calculus.WellTyped TC hiding (Ctx)

⟦_,_⟧e : ∀ {ν η} → E.Effect η → TCtx ν η → C.Type (ν N+ η)
⟦ evar x , m ⟧e = C.tvar (lookup-evar m x)
⟦ has read , m ⟧e = C.tc CanRead
⟦ has write , m ⟧e = C.tc CanWrite
⟦ has throw , m ⟧e = C.tc CanThrow
⟦ has io , m ⟧e = C.tc CanIO
⟦_,_⟧e {ν} {η} (H x) m  = C.∀' (subst C.Type (+-suc ν η) (⟦ x , m +evar ⟧e))

⟦_,_⟧efs : ∀ {ν η} → E.Effects η → TCtx ν η → C.Type (ν N+ η)
⟦ List.[] , m ⟧efs = C.tc unit
⟦ e List.∷ List.[] , m ⟧efs = ⟦ e , m ⟧e
⟦ e List.∷ d List.∷ ef , m ⟧efs = C.rec (fromList (List.map (λ e → ⟦ e , m ⟧e) (e & d & ef)))

⇒-wrap : ∀ {ν η} → E.Effects η → TCtx ν η → C.Type (ν N+ η) → C.Type (ν N+ η)
⇒-wrap List.[] m t = t
⇒-wrap (e List.∷ List.[]) m t = ⟦ e , m ⟧e C.⇒ t
⇒-wrap (e List.∷ d List.∷ es) m t = ⟦ e & d & es , m ⟧efs C.⇒ t

ρ-wrap : ∀ {ν η n} → E.Effects η → TCtx ν η → C.Term (ν N+ η) n → C.Term (ν N+ η) n
ρ-wrap List.[] m t = t
ρ-wrap (e List.∷ List.[]) m t = C.ρ ⟦ e , m ⟧e (C.tmtm-weaken t)
ρ-wrap (e List.∷ d List.∷ es) m t = C.ρ ⟦ e & d & es , m ⟧efs (C.tmtm-weaken t)

ρ-unwrap : ∀ {ν η n} → E.Effects η → TCtx ν η → C.Term (ν N+ η) n → C.Term (ν N+ η) n
ρ-unwrap List.[] m t = t
ρ-unwrap (e List.∷ es) m t = t C.⟨⟩

⟦_,_⟧tp : ∀ {ν η} → E.Type ν η → TCtx ν η → C.Type (ν N+ η)
⟦ unit , m ⟧tp = C.tc unit
⟦ tvar x , m ⟧tp = C.tvar (lookup-tvar m x)
⟦ a →[ es ] b , m ⟧tp = ⟦ a , m ⟧tp C.→' (⇒-wrap es m ⟦ b , m ⟧tp)
⟦ ∀' t , m ⟧tp = C.∀' ⟦ t , m +tvar ⟧tp
⟦_,_⟧tp {ν} {η} (H t) m = C.∀' (subst C.Type (+-suc ν η) ⟦ t , m +evar ⟧tp)

⟦_,_⟧ctx : ∀ {ν η n} → E.Ctx ν η n → TCtx ν η → C.Ktx (ν N+ η) n
⟦ C , m ⟧ctx = map (flip ⟦_,_⟧tp m) C , List.[]

infixl 8 ⟦_+_,_⟧tpef
⟦_+_,_⟧tpef : ∀ {ν η} → E.Type ν η → E.Effects η → TCtx ν η → C.Type (ν N+ η)
⟦ a + es , m ⟧tpef = ⇒-wrap es m ⟦ a , m ⟧tp

-- Effectful values (i.e.: as soon as evaluated they have an effect)
-- require the implicit Can* to be in scope, or they won't typecheck.
-- Delayed effects are represented by wrapping the bodies in rules that take implicit args.
-- To make the types match, the application complement of the delaying constructor should
-- 'unwrap' the body using implicit application.
-- To make sure the required implicits are in scope, it wraps the whole thing in another rule.
-- The operations that 'delay' effects are λ', Λ, H, but the bodies of Λ and H have to be pure
-- and thus don't need to be wrapped.

-- type driven translation of effect terms into
-- terms from the implicit calculus
⟦_,_⟧ : ∀ {ν η n} {Γ : E.Ctx ν η n} {t a e} → Γ E.⊢ t ∈ a + e → TCtx ν η → C.Term (ν N+ η) n

-- pure primitives
⟦ tt , m ⟧ = C.new unit
⟦ var x , m ⟧ = C.var x

-- effectful primitive values
⟦ does c , m ⟧ =
  (ρ-wrap (has c & pure) m (C.new unit)) C.⟨⟩

-- effect-delaying
⟦ λ' {e = es} a wt , m ⟧ =
  C.λ' ⟦ a , m ⟧tp
    (ρ-wrap (effects wt) m ⟦ wt , m ⟧)
⟦ Λ wt , m ⟧ =
  C.Λ
    ⟦ wt , m +tvar ⟧
⟦_,_⟧ {ν} {η} {n} (H wt) m =
  C.Λ (subst (flip C.Term n) (+-suc ν η) ⟦ wt , m +evar ⟧)

-- unleashes the delayed effects
⟦ wt₁ · wt₂ , m ⟧ =
  ρ-wrap (effects $ wt₁ · wt₂) m
    (ρ-unwrap (effects wt₁) m (⟦ wt₁ , m ⟧ C.· ⟦ wt₂ , m ⟧))
⟦ wt [ b ] , m ⟧ =
  ⟦ wt , m ⟧ C.[ ⟦ b , m ⟧tp ]
⟦ wt ! f , m ⟧ =
  ⟦ wt , m ⟧ C.[ ⟦ f , m ⟧efs ]

module Lemmas where
  -- lookup in and interpreted context Γ is equivalent to interpreting a type, looked up in K
  lookup⋆⟦⟧ctx : ∀ {ν η n} (C : Ctx ν η n) (m : TCtx ν η) x →
                 lookup x (proj₁ ⟦ C , m ⟧ctx) ≡ ⟦ lookup x C , m ⟧tp
  lookup⋆⟦⟧ctx C m x = sym $ lookup⋆map C (flip ⟦_,_⟧tp m) x 

  postulate tp-weaken⋆⟦⟧ctx : ∀ {ν η n} (C : Ctx ν η n) (m : TCtx ν η) →
                              ⟦ ctx-tp-weaken C , (m +tvar) ⟧ctx ≡ C.ktx-weaken ⟦ C , m ⟧ctx
  postulate ef-weaken⋆⟦⟧ctx : ∀ {ν η n} (C : Ctx ν η n) (m : TCtx ν η) →
                    subst (flip C.Ktx n) (+-suc ν η) ⟦ ctx-ef-weaken C , (m +evar) ⟧ctx ≡
                    (C.ktx-weaken ⟦ C , m ⟧ctx)
  --ef-weaken⋆⟦⟧ctx c m = {!!}

open Lemmas

{-
⟦⟧-preserves : ∀ {ν η n} {Γ : E.Ctx ν η n} {t a e} →
  (wt : Γ E.⊢ t ∈ a + e) → (m : TCtx ν η) →
  ⟦ Γ , m ⟧ctx C.⊢ ⟦ wt , m ⟧ ∈ ⟦ a + e , m ⟧tpef
⟦⟧-preserves {Γ = Γ} (var x) m =
  subst (λ u → _ C.⊢ C.var x ∈ u) (lookup⋆⟦⟧ctx Γ m x) (C.var x)
⟦⟧-preserves (λ' {e = List.[]} a wt) m =
  C.λ' ⟦ a , m ⟧tp (⟦⟧-preserves wt m)
⟦⟧-preserves (λ' {e = e List.∷ List.[]} a wt) m =
  C.λ' ⟦ a , m ⟧tp (C.ρ ⟦ e , m ⟧e {!!})
  -- (C.TermTermLemmas.weaken (⟦⟧-preserves wt m))
  -- this is a tough one: we bring necessary implicits in scope here through the rule
  -- this has to be somehow represented in the context translation
⟦⟧-preserves (λ' {e = e List.∷ d List.∷ es} a wt) m =
  C.λ' ⟦ a , m ⟧tp (C.ρ ⟦ e & d & es , m ⟧efs {!!})
⟦⟧-preserves (wt₁ · wt₂) m = {!!}
⟦⟧-preserves {Γ = Γ} (Λ wt) m with ⟦⟧-preserves wt (m +tvar)
⟦⟧-preserves {Γ = Γ} (Λ {a = a} wt) m | ih =
  C.Λ (subst (λ u → u C.⊢ C.erase ih ∈ ⟦ a , m +tvar ⟧tp) (tp-weaken⋆⟦⟧ctx Γ m) ih)
⟦⟧-preserves (wt [ b ]) m = {!!}
⟦⟧-preserves {Γ = Γ} (H wt) m with ⟦⟧-preserves wt (m +evar)
⟦⟧-preserves {ν = ν} {η = η} {n = n} {Γ = Γ} (H {a = a} wt) m | ih = C.Λ {!!} --res
    where
      Γ' = C.ktx-weaken ⟦ Γ , m ⟧ctx
      t' = subst (flip C.Term n) (+-suc ν η) (C.erase ih)
      a' = subst C.Type (+-suc ν η) ⟦ a , m +evar ⟧tp
      res' : ⟦ ctx-ef-weaken Γ , m +evar ⟧ctx C.⊢ ⟦ wt , m +evar ⟧ ∈ ⟦ a , m +evar ⟧tp
      res' = ih
      -- l : C.ktx-weaken ⟦ Γ , m ⟧ctx C.⊢ ⟦ wt , m +evar ⟧ ∈ ⟦ a , m +evar ⟧tp
      -- l = subst (flip C.Ktx n) (sym $ +-suc ν η) (C.ktx-weaken ⟦ C , m ⟧ctx)
      -- l = subst (λ u → u C.⊢ _ ∈ _) (ef-weaken⋆⟦⟧ctx Γ (m +evar)) res'
      -- res : C.ktx-weaken ⟦ Γ , m ⟧ctx C.⊢ t' ∈ a'
      -- res = {!ih!}
      -- res = subst₂ (λ u v → C._⊢_∈_ Γ' u v) (sym $ +-suc ν η) (ef-weaken⋆⟦⟧ctx Γ m)
⟦⟧-preserves (wt ! f) m with ⟦⟧-preserves wt m
⟦⟧-preserves (wt ! f) m | ih = {!ih C.[ ⟦ f , m ⟧efs ]!}
⟦⟧-preserves (does c) m = (C.ρ ⟦ has c , m ⟧e (C.WtTermLemmas.weaken $ C.new unit))
⟦⟧-preserves tt m = C.new unit

-}
