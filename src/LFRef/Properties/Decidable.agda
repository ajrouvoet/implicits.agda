module LFRef.Properties.Decidable where

open import Prelude hiding (sym)
open import Relation.Unary
open import Relation.Nullary.Decidable as DecM
open import Data.Fin.Properties as FinP using ()
open import Data.List
open import Data.Vec
open import Data.Vec.Properties
open import Function.Inverse
open import Extensions.List as List↑ using ()
open import Extensions.Vec as Vec↑ using ()
open import Relation.Binary.List.Pointwise using (decidable-≡)
open import Relation.Binary.HeterogeneousEquality as Het using ()

open import LFRef.Syntax hiding (subst)
open import LFRef.Welltyped

module DecidableEquality where
  -- termination checker has trouble with mapping
  -- recursively over the arguments of constructors; inlining would prove this terminating
  {-# TERMINATING #-}
  _tm≟_ : ∀ {n} (a b : Term n) → Dec (a ≡ b)
  var x tm≟ var x' with (x FinP.≟ x')
  ... | yes refl = yes refl
  ... | no neq = no (λ{ refl → neq refl })
  var x tm≟ loc x₁ = no (λ ())
  var x tm≟ unit = no (λ ())
  var x tm≟ con fn ts = no (λ ())
  loc x tm≟ var x₁ = no (λ ())
  loc x tm≟ loc x' with x ≟ x'
  ... | yes refl = yes refl
  ... | no neq = no (λ{ refl → neq refl })
  loc x tm≟ unit = no (λ ())
  loc x tm≟ con fn ts = no (λ ())
  unit tm≟ var x = no (λ ())
  unit tm≟ loc x = no (λ ())
  unit tm≟ unit = yes refl
  unit tm≟ con fn ts = no (λ ())
  con fn ts tm≟ var x = no (λ ())
  con fn ts tm≟ loc x = no (λ ())
  con fn ts tm≟ unit = no (λ ())
  con fn ts tm≟ con fn' ts' with fn ≟ fn'
  ... | no neq = no (λ{ refl → neq refl })
  ... | yes refl with decidable-≡ _tm≟_ ts ts'
  ... | no neq = no (λ{ refl → neq refl })
  ... | yes refl = yes refl

  -- decidable type equality
  _ty≟_ : ∀ {n} (a b : Type n) → Dec (a ≡ b)
  (x [ ts ]) ty≟ (x' [ ts' ]) with x ≟ x'
  ... | no neq = no (λ{ refl → neq refl })
  ... | yes refl with decidable-≡ _tm≟_ ts ts'
  ... | yes refl = yes refl
  ... | no neq = no (λ{ refl → neq refl })
  (x [ ts ]) ty≟ Ref b = no (λ ())
  (x [ ts ]) ty≟ Unit = no (λ ())
  Ref a ty≟ (x [ ts ]) = no (λ ())
  Ref a ty≟ Ref b with a ty≟ b
  ... | yes refl = yes refl
  ... | no neq = no (λ{ refl → neq refl })
  Ref a ty≟ Unit = no (λ ())
  Unit ty≟ (x [ ts ]) = no (λ ())
  Unit ty≟ Ref b = no (λ ())
  Unit ty≟ Unit = yes refl

module UniqueTypings where
  unique-tm-type : ∀ {n a b} 𝕊 Σ Γ (t : Term n) → 𝕊 , Σ , Γ ⊢ t ∶ a → 𝕊 , Σ , Γ ⊢ t ∶ b → a ≡ b
  unique-tm-type 𝕊 Σ Γ .unit unit unit = refl
  unique-tm-type 𝕊 Σ Γ .(var _) (var x) (var x') with Vec↑.[]=-functional Γ _ x x'
  ... | refl = refl
  unique-tm-type 𝕊 Σ Γ .(loc _) (loc x) (loc x') with List↑.[]=-functional Σ _ x x'
  ... | refl = refl
  unique-tm-type 𝕊 Σ Γ .(con _ _) (con c ts refl) (con c' ts' refl)
    with List↑.[]=-functional _ _ c c'
  ... | refl = refl

module DecidableTypability where
  open UniqueTypings
  open DecidableEquality

  mutual
    type-tm : ∀ {n} 𝕊 Σ Γ (t : Term n) → Dec (∃ λ a → 𝕊 , Σ , Γ ⊢ t ∶ a)
    type-tm 𝕊 Σ Γ (var x) =
      yes (, var (proj₂ (Vec↑.strong-lookup _ _)))
    type-tm 𝕊 Σ Γ (loc x) =
      DecM.map′
        (λ{ (_ , p)  → Ref _ , loc p})
        (λ{ (_ , loc p) → _ , p })
        (List↑.dec-lookup x Σ)
    type-tm 𝕊 Σ Γ unit = yes (Unit , unit)
    type-tm 𝕊 Σ Γ (con c ts) with (List↑.dec-lookup c (Sig.constructors 𝕊))
    ... | no ¬p = no (λ{ (._ , con p _ _) → ¬p (, p)})
    ... | yes (p , z) with typecheck-tele 𝕊 Σ Γ ts (weaken+-tele _ (ConType.args p))
    ... | no ¬q = no lem
      where
        lem : ¬ ∃ λ ty → 𝕊 , Σ , Γ ⊢ (con c ts) ∶ ty
        lem (._ , con x q p) with List↑.[]=-functional _ _ z x
        ... | refl = ¬q q
    ... | yes q = yes (, con z q (tele-fit-length q))

    -- deciding whether a term matches a given type follows from
    -- typability with unique type assignments
    typecheck-tm : ∀ {n} 𝕊 Σ Γ (t : Term n) a → Dec (𝕊 , Σ , Γ ⊢ t ∶ a)
    typecheck-tm 𝕊 Σ Γ t a with type-tm 𝕊 Σ Γ t
    ... | no nwt = no (λ wta → nwt (, wta))
    ... | yes (a' , wta') with a ty≟ a'
    ... | yes refl = yes wta'
    ... | no neq = no (λ wta → neq (unique-tm-type 𝕊 Σ Γ _ wta wta'))

    typecheck-tele : ∀ {n m } 𝕊 Σ Γ (ts : List (Term n)) → (T : Tele n m) → Dec (𝕊 , Σ , Γ ⊢ ts ∶ⁿ T)
    typecheck-tele 𝕊 Σ Γ [] ε = yes ε
    typecheck-tele 𝕊 Σ Γ [] (x ⟶ T) = no (λ ())
    typecheck-tele 𝕊 Σ Γ (x ∷ ts) ε = no (λ ())
    typecheck-tele 𝕊 Σ Γ (x ∷ ts) (ty ⟶ T)
      with typecheck-tm 𝕊 Σ Γ x ty
    ... | no ¬x∶ty = no (λ{ (x∶ty ⟶ _) → ¬x∶ty x∶ty })
    ... | yes x∶ty with typecheck-tele 𝕊 Σ Γ ts (T tele/ (sub x))
    ... | yes ts∶T = yes (x∶ty ⟶ ts∶T)
    ... | no ¬ts∶T = no (λ{ (_ ⟶ ts∶T) → ¬ts∶T ts∶T })

  {-}
  type : ∀ {n} 𝕊 Σ Γ (e : Exp n) → Dec (∃ λ a → 𝕊 , Σ , Γ ⊢ₑ e ∶ a)
  type 𝕊 Σ Γ (tm t) = DecM.map′
    (λ x → _ , (tm (proj₂ x)))
    (λ{ (_ , tm x) → , x})
    (type-tm 𝕊 Σ Γ t)
  type 𝕊 Σ Γ (fn ·★ as) = {!!}
  -- this case is problematic; we have to figure out if
  -- the type returned from the body is the weakening of some other type.
  -- which is not (easily) decidable
  type 𝕊 Σ Γ (lett e₁ e₂) with type 𝕊 Σ Γ e₁
  ... | no nwte₁ = {!!}
  ... | yes (ty , wte₁) with type 𝕊 Σ (ty :+: Γ) e₂
  ... | no nwte₂ = {!!}
  ... | yes (ty' , wte₂) = yes (ty' , (lett wte₁ wte₂))
  type 𝕊 Σ Γ (ref e) = {!!}
  type 𝕊 Σ Γ (! e) = {!!}
  type 𝕊 Σ Γ (e ≔ e₁) = {!!}
  -}

  typecheck : ∀ {n} 𝕊 Σ Γ (e : Exp n) a → Dec (𝕊 , Σ , Γ ⊢ₑ e ∶ a)
  typecheck 𝕊 Σ Γ (tm t) a = DecM.map′
    (λ x → (tm x))
    (λ{ (tm x) → x})
    (typecheck-tm 𝕊 Σ Γ t a)
  typecheck {n} 𝕊 Σ Γ (fn ·★ ts) a with List↑.dec-lookup fn (Sig.funs 𝕊)
  ... | no ¬fn! = no (λ { (fn! ·★ _) → ¬fn! (, fn!) })
  ... | yes (φ , fn!) with typecheck-tele 𝕊 Σ Γ ts (weaken+-tele _ (Fun.args φ))
  ... | no ¬ts∶T = no lem
    where
      lem : ¬ 𝕊 , Σ , Γ ⊢ₑ (fn ·★ ts) ∶ a
      lem (fn!' ·★ ts∶T) with List↑.[]=-functional _ _ fn! fn!'
      ... | refl = ¬ts∶T ts∶T
  ... | yes ts∶T with ((Fun.returntype φ) fun[ ts / (tele-fit-length ts∶T) ]) ty≟ a
  ... | yes refl = yes (subst (λ x → _ , _ , _ ⊢ₑ _ ∶ x) refl (fn! ·★ ts∶T))
  ... | no neq = no lem
    where
      lem : ¬ 𝕊 , Σ , Γ ⊢ₑ (fn ·★ ts) ∶ a
      lem (fn!' ·★ ts∶T') with tele-fit-length ts∶T | tele-fit-length ts∶T' |
        List↑.[]=-functional _ _ fn! fn!'
      ... | refl | refl | refl = neq refl
  typecheck 𝕊 Σ Γ (lett e₁ a e₂) b with typecheck 𝕊 Σ Γ e₁ a
  ... | no nwte₁ = no (λ{ (lett wta _) → nwte₁ wta })
  ... | yes wte₁ with typecheck 𝕊 Σ (a :+: Γ) e₂ (weaken₁-tp b)
  ... | no nwte₂ = no (λ{ (lett _ wtb) → nwte₂ wtb})
  ... | yes wte₂ = yes (lett wte₁ wte₂)
  typecheck 𝕊 Σ Γ (ref e) (Ref a) = DecM.map′
    ref (λ{ (ref wte) → wte })
    (typecheck 𝕊 Σ Γ e a)
  typecheck 𝕊 Σ Γ (ref e) (x [ ts ]) = no (λ ())
  typecheck 𝕊 Σ Γ (ref e) Unit = no (λ ())
  typecheck 𝕊 Σ Γ (! e) a = DecM.map′
    !_ (λ{ (! wte) → wte })
    (typecheck 𝕊 Σ Γ e (Ref a))
  typecheck 𝕊 Σ Γ (l ≔ r) = {!!}
