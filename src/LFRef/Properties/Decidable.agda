module LFRef.Properties.Decidable where

open import Prelude
open import Relation.Unary
open import Relation.Nullary.Decidable as DecM
open import Data.Fin.Properties as FinP using ()
open import Data.List
open import Data.Vec
open import Data.Vec.Properties
open import Function.Inverse hiding (_∘_; sym)
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
  unique-tm-type : ∀ {n a b 𝕊 Σ Γ} {t : Term n} → 𝕊 , Σ , Γ ⊢ t ∶ a → 𝕊 , Σ , Γ ⊢ t ∶ b → a ≡ b
  unique-tm-type unit unit = refl
  unique-tm-type (var x) (var x') with Vec↑.[]=-functional _ _ x x'
  ... | refl = refl
  unique-tm-type (loc x) (loc x') with List↑.[]=-functional _ _ x x'
  ... | refl = refl
  unique-tm-type (con c ts refl) (con c' ts' refl)
    with List↑.[]=-functional _ _ c c'
  ... | refl = refl

  unique-type : ∀ {n a b 𝕊 Σ Γ} {e : Exp n} → 𝕊 , Σ , Γ ⊢ₑ e ∶ a → 𝕊 , Σ , Γ ⊢ₑ e ∶ b → a ≡ b
  unique-type (tm x) (tm y) = unique-tm-type x y
  unique-type (fn ·★ ts) (fn' ·★ ts') with List↑.[]=-functional _ _ fn fn' |
    tele-fit-length ts | tele-fit-length ts'
  ... | refl | refl | refl = refl
  unique-type (ref p) (ref q) = cong Ref (unique-type p q)
  unique-type (! p) (! q) with unique-type p q
  ... | refl = refl
  unique-type (p ≔ q) (p' ≔ q') = refl

  elim-mistype : ∀ {n a b 𝕊 Σ Γ} {e : Exp n} →
                   𝕊 , Σ , Γ ⊢ₑ e ∶ a → 𝕊 , Σ , Γ ⊢ₑ e ∶ b → ¬ (a ≢ b)
  elim-mistype p q with unique-type p q
  ... | refl = λ neq → neq refl

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
    ... | no neq = no (λ wta → neq (unique-tm-type wta wta'))

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

  type : ∀ {n} 𝕊 Σ Γ (e : Exp n) → Dec (∃ λ a → 𝕊 , Σ , Γ ⊢ₑ e ∶ a)
  type 𝕊 Σ Γ (tm t) = DecM.map′
    (λ{ (_ , x ) → , (tm x)})
    (λ{ (_ , tm x) → , x})
    (type-tm 𝕊 Σ Γ t)
  type {n} 𝕊 Σ Γ (fn ·★ ts) with List↑.dec-lookup fn (Sig.funs 𝕊)
  ... | no ¬fn! = no (λ { (_ , (fn! ·★ _)) → ¬fn! (, fn!) })
  ... | yes (φ , fn!) with typecheck-tele 𝕊 Σ Γ ts (weaken+-tele _ (Fun.args φ))
  ... | no ¬ts∶T = no lem
    where
      lem : ¬ ∃ λ a → 𝕊 , Σ , Γ ⊢ₑ (fn ·★ ts) ∶ a
      lem (_ , (fn!' ·★ ts∶T)) with List↑.[]=-functional _ _ fn! fn!'
      ... | refl = ¬ts∶T ts∶T
  ... | yes ts∶T = yes (, fn! ·★ ts∶T)
  type 𝕊 Σ Γ (ref e) with (type 𝕊 Σ Γ e)
  ... | no ¬wte = no (λ{ (.(Ref _) , ref wte) → ¬wte (, wte)})
  ... | yes (a , wte) = yes (, ref wte)
  type 𝕊 Σ Γ (! e) with (type 𝕊 Σ Γ e)
  ... | no ¬wte = no ((λ{ (x , (! wte)) → ¬wte (, wte) }))
  type 𝕊 Σ Γ (! e) | yes (x [ ts ] , wte) =
    no λ{ (_ , ! wte') → elim-mistype wte  wte' (λ ()) }
  type 𝕊 Σ Γ (! e) | yes (Unit , wte) =
    no λ{ (_ , ! wte' ) → elim-mistype wte wte' (λ ()) }
  type 𝕊 Σ Γ (! e) | yes (Ref a , wte) = yes (_ , (! wte))
  type 𝕊 Σ Γ (l ≔ r) with type 𝕊 Σ Γ l | type 𝕊 Σ Γ r
  ... | no ¬wtl | _ = no (λ{ (_ , wtl ≔ _ ) → ¬wtl (, wtl) })
  ... | _ | no ¬wtr = no (λ{ (_ , _ ≔ wtr ) → ¬wtr (, wtr) })
  ... | yes (x [ ts ] , wtl) | (yes (b , wtr)) =
    no (λ{ (_ , wtl' ≔ wtr) → elim-mistype wtl wtl' (λ ())})
  ... | yes (Unit , wtl) | (yes (b , wtr)) =
    no (λ{ (_ , wtl' ≔ wtr) → elim-mistype wtl wtl' (λ ())})
  ... | yes (Ref a , wtl) | yes (b , wtr) with a ty≟ b
  ... | yes refl = yes (, wtl ≔ wtr)
  ... | no neq = no lem
    where
      lem : ¬ ∃ λ a → 𝕊 , Σ , Γ ⊢ₑ (l ≔ r) ∶ a
      lem (.Unit , (wtl' ≔ wtr')) with unique-type wtl wtl'
      ... | refl = elim-mistype wtr wtr' (neq ∘ sym)

  typecheck : ∀ {n} 𝕊 Σ Γ (e : Exp n) a → Dec (𝕊 , Σ , Γ ⊢ₑ e ∶ a)
  typecheck 𝕊 Σ Γ e a with type 𝕊 Σ Γ e
  ... | no ¬wte = no (λ wte → ¬wte (, wte))
  ... | yes (a' , wte) with a' ty≟ a
  ... | yes refl = yes wte
  ... | no neq = no (λ{ wte' → elim-mistype wte wte' neq })

  typecheck-seq : ∀ {n} 𝕊 Σ Γ (e : SeqExp n) a → Dec (𝕊 , Σ , Γ ⊢ₛ e ∶ a)
  typecheck-seq 𝕊 Σ Γ (lett e c) a with type 𝕊 Σ Γ e
  ... | no ¬wte = no (λ{ (lett wte _ ) → ¬wte (, wte)})
  ... | yes (b , wte) with typecheck-seq 𝕊 Σ (b :+: Γ) c (weaken₁-tp a)
  ... | yes wtc = yes (lett wte wtc)
  ... | no ¬wtc = no lem
    where
      lem : ¬ 𝕊 , Σ , Γ ⊢ₛ lett e c ∶ a
      lem (lett wte' wtc) with unique-type wte wte'
      ... | refl = ¬wtc wtc
  typecheck-seq 𝕊 Σ Γ (ret e) a = DecM.map′ ret (λ{ (ret wte) → wte }) (typecheck 𝕊 Σ Γ e a)
