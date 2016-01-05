
module Extensions.Nat where

open import Prelude
open import Data.Nat.Base
open import Data.Nat.Properties.Simple
open import Data.Nat.Properties

m+1+n≡1+m+n : ∀ m n → m N+ suc n ≡ suc (m N+ n)
m+1+n≡1+m+n zero    n = refl
m+1+n≡1+m+n (suc m) n = cong suc (m+1+n≡1+m+n m n)

<-+ : ∀ {m n m' n'} → m N≤ m' → n N≤ n' → m N+ n N≤ m' N+ n'
<-+ {zero} {zero} z≤n z≤n = z≤n
<-+ {suc m} (s≤s m<m') x = s≤s (<-+ m<m' x)
<-+ {zero} {suc n} {zero} z≤n (s≤s n<n') = s≤s n<n'
<-+ {zero} {suc n} {suc m'} z≤n (s≤s n<n') = s≤s (<-+ {m' = m'} z≤n (≤-step n<n'))
