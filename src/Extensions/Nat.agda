
module Extensions.Nat where

open import Prelude
open import Data.Nat.Base
open import Data.Nat.Properties.Simple
open import Data.Nat.Properties

m+1+n≡1+m+n : ∀ m n → m + suc n ≡ suc (m + n)
m+1+n≡1+m+n zero    n = refl
m+1+n≡1+m+n (suc m) n = cong suc (m+1+n≡1+m+n m n)

<-+ : ∀ {m n m' n'} → m ≤ m' → n ≤ n' → m + n ≤ m' + n'
<-+ {zero} {zero} z≤n z≤n = z≤n
<-+ {suc m} (s≤s m<m') x = s≤s (<-+ m<m' x)
<-+ {zero} {suc n} {zero} z≤n (s≤s n<n') = s≤s n<n'
<-+ {zero} {suc n} {suc m'} z≤n (s≤s n<n') = s≤s (<-+ {m' = m'} z≤n (≤-step n<n'))

<-unique : ∀ {i u} (p q : i < u) → p ≡ q
<-unique (s≤s z≤n) (s≤s z≤n) = refl
<-unique (s≤s (s≤s p)) (s≤s (s≤s q)) = sym (cong s≤s (<-unique (s≤s q) (s≤s p)))
