module Extensions.ListFirstFunctional where

open import Prelude hiding (_⊔_)
open import Level

private
    lemma : ∀ {a b} {A : Set a} {P : A → Set b} (decP : ∀ a → (Dec $ P a)) v {x y} →
            any decP (x List.∷ v) ≡ yes (there {x = x} y) → ¬ P x
    lemma decP v {x} {y} eq p with decP x
    lemma decP v () p         | yes _
    lemma decP v eq p         | no ¬p = ¬p p

-- first is functionally defined as the element matched by 'any'
First : ∀ {a b} {A : Set a} {P : A → Set b} (decP : ∀ a → (Dec $ P a)) → List A → Set (a ⊔ b)
First f v = ∃ λ m → any f v ≡ yes m

private
    There : ∀ {a b} {A : Set a} {P : A → Set b} {f v} → (f : First {P = P} f v) → Set
    There (here px , _) = ⊥
    There (there _ , _) = ⊤

    head-first : ∀ {a b} {A : Set a} {P : A → Set b} {f v} → First {P = P} f v → A
    head-first (here {x} _ , _) = x
    head-first (there {x} _ , _) = x

-- we can recover the negative evidence even though Any does not "save it" for there-instances
there⟶¬x' : ∀ {a b} {A : Set a} {P : A → Set b} {decP v} →
            (f : First {P = P} decP v) → {x : There f} → ¬ P (head-first f)
there⟶¬x' (here px , proj₂) {x = ()}
there⟶¬x' {P = P} {decP = decP} (there {x = x'} {xs = xs} tail , proj₂) px with lemma decP xs
there⟶¬x' {P = P} {decP = decP} (there {x = x'} {xs = xs} tail , proj₂) px | ¬px = ¬px proj₂ px
