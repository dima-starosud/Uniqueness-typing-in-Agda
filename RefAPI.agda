module RefAPI where

open import Context

open import Function
open import Data.Nat
open import Data.String
open import Data.List
open import Data.List.Any
open import Data.Product
open import Data.Unit using (Unit; unit; ⊤)
open import Relation.Binary.Core

open import Relation.Binary.PropositionalEquality hiding ([_]) renaming (cong to ≡-cong; cong₂ to ≡-cong₂)
open import Relation.Binary.PropositionalEquality.Core renaming (sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.TrustMe

postulate
  nativeRef : (A : Set) → Set
  nativeNewRef-ℕ : (init : ℕ) → nativeRef ℕ
  nativeSetRef-ℕ : ℕ → nativeRef ℕ
  nativeGetRef-ℕ : nativeRef ℕ → ℕ
  nativeAddRef-ℕ : nativeRef ℕ → nativeRef ℕ → nativeRef ℕ
  nativeFreeRef-ℕ : nativeRef ℕ → Unit

data Exact {ℓ} {A : Set ℓ} : A → Set ℓ where
  exact : ∀ a → Exact a

Ref-ℕ : ℕ → Set
Ref-ℕ a = Σ[ native ∶ nativeRef ℕ ] nativeGetRef-ℕ native ≡ a

proofNewRef-ℕ : (a : ℕ) → Ref-ℕ a
proofNewRef-ℕ a = nativeNewRef-ℕ a , trustMe

proofSetRef-ℕ : (a : ℕ) → Ref-ℕ a
proofSetRef-ℕ a = nativeSetRef-ℕ a , trustMe

proofGetRef-ℕ : {a : ℕ} → Ref-ℕ a → Exact a
proofGetRef-ℕ (r , p) = ≡-elim′ Exact p (exact $ nativeGetRef-ℕ r)

proofAddRef-ℕ : {a₁ a₂ : ℕ} → Ref-ℕ a₁ → Ref-ℕ a₂ → Ref-ℕ (a₁ + a₂)
proofAddRef-ℕ (r₁ , _) (r₂ , _) = nativeAddRef-ℕ r₁ r₂ , trustMe

proofFreeRef-ℕ : {a : ℕ} → Ref-ℕ a → Unit
proofFreeRef-ℕ (r , _) = nativeFreeRef-ℕ r

newRef-ℕ : ∀ a n → Transformer! [] [(n , Unique (Ref-ℕ a))]
newRef-ℕ a n v nr-v []⊆v nr-v∪n = w , (≡⇒≋ $ ≡-trans p₁ p₂) where
    w = v ∪ [(n , Unique (Ref-ℕ a) , unique (proofNewRef-ℕ a))]
    p₁ : types (v ∪ [(n , Unique (Ref-ℕ a) , _)]) ≡ types v ∪ [(n , Unique (Ref-ℕ a))]
    p₁ = t-x∪y v [(n , Unique (Ref-ℕ a) , _)]
    p₂ : types v ∪ [(n , Unique (Ref-ℕ a))] ≡ types v ∖∖ [] ∪ [(n , Unique (Ref-ℕ a))]
    p₂ = ≡-cong (λ x → x ∪ [(n , Unique (Ref-ℕ a))]) (≡-sym $ t∖[]≡t $ types v)

setRef-ℕ : ∀ {a₀} a₁ n → Transformer! [(n , Unique (Ref-ℕ a₀))] [(n , Unique (Ref-ℕ a₁))]
setRef-ℕ a₁ n v nr-v []⊆v nr-v∪n = w , p {-(≡⇒≋ $ ≡-trans p₁ p₂)-} where
    w = v ∖∖ [ n ] ∪ [(n , Unique (Ref-ℕ a₁) , unique (proofNewRef-ℕ a₁))]
    p : _
    p = _
