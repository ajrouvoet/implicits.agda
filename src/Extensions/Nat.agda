
module Extensions.Nat where

open import Prelude

m+1+n≡1+m+n : ∀ m n → m N+ suc n ≡ suc (m N+ n)
m+1+n≡1+m+n zero    n = refl
m+1+n≡1+m+n (suc m) n = cong suc (m+1+n≡1+m+n m n)
