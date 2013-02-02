module RefAPITest where

open import RefAPI

open import Function
open import Data.Nat
open import Data.Product

new = new-ℕ
_++ = inc-ℕ
*_ = get-ℕ
free = free-ℕ

tr : (n : ℕ) → Transformer! [] [(_ , Pure (Exact $ suc n))]
tr i = "r" := new i ⇒⟦ refl ⟧⇒  -- new ℕ(i)
       "r" ++       ⇒⟦ refl ⟧⇒  -- r++
       "j" := * "r" ⇒⟦ refl ⟧⇒  -- j := *r
       free "r"

p : ∀ n → getExact (extract $ tr n) ≡ suc n
p = ≡-exact ∘ extract ∘ tr
