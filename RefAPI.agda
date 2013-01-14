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
  -- initializes reference with passed value
  nativeNewRef-ℕ : ℕ → nativeRef ℕ
  -- assignment addition: first argument is updated
  nativeUpdAddRef-ℕ : nativeRef ℕ → nativeRef ℕ → Unit
  nativeGetRef-ℕ : nativeRef ℕ → ℕ
  nativeFreeRef-ℕ : nativeRef ℕ → Unit

data Exact {ℓ} {A : Set ℓ} : A → Set ℓ where
  exact : ∀ a → Exact a

Ref-ℕ : ℕ → Set
Ref-ℕ a = Σ[ native ∶ nativeRef ℕ ] nativeGetRef-ℕ native ≡ a

proofNewRef-ℕ : ∀ a → Ref-ℕ a
proofNewRef-ℕ a = nativeNewRef-ℕ a , trustMe

proofUpdAddRef-ℕ : ∀ {a₁ a₂} → Ref-ℕ a₁ → Ref-ℕ a₂ → Ref-ℕ (a₁ + a₂)
proofUpdAddRef-ℕ (r₁ , _) (r₂ , _) = r₁ , trustMe where
  u = nativeUpdAddRef-ℕ r₁ r₂

proofGetRef-ℕ : ∀ {a} → Ref-ℕ a → Exact a
proofGetRef-ℕ (r , p) = ≡-elim′ Exact p (exact $ nativeGetRef-ℕ r)

proofFreeRef-ℕ : {a : ℕ} → Ref-ℕ a → Unit
proofFreeRef-ℕ (r , _) = nativeFreeRef-ℕ r

newRef-ℕ : ∀ a n → Transformer! [] [(n , Unique (Ref-ℕ a))]
newRef-ℕ a n v nr-v []⊆v nr-v∪n = w , (≡⇒≋ $ ≡-trans p₁ p₂) where
    w = v ∪ [(n , Unique (Ref-ℕ a) , unique (proofNewRef-ℕ a))]
    p₁ : types (v ∪ [(n , Unique (Ref-ℕ a) , _)]) ≡ types v ∪ [(n , Unique (Ref-ℕ a))]
    p₁ = t-x∪y v [(n , Unique (Ref-ℕ a) , _)]
    p₂ : types v ∪ [(n , Unique (Ref-ℕ a))] ≡ types v ∖∖ [] ∪ [(n , Unique (Ref-ℕ a))]
    p₂ = ≡-cong (λ x → x ∪ [(n , Unique (Ref-ℕ a))]) (≡-sym $ t∖[]≡t $ types v)

+=Ref-ℕ : ∀ {a₁} {a₂} n₁ n₂ → Transformer! [(n₁ , Unique (Ref-ℕ a₀))] [(n , Unique (Ref-ℕ a₁))]
+=Ref-ℕ a₁ n v nr-v n⊆v nr-v∪n = w , (≡⇒≋ $ ≡-trans p₁ p₂) where
    r = Unique.get ∘ getBySignature ∘ n⊆v $ here refl
    w = v ∖∖ [ n ] ∪ [(n , Unique (Ref-ℕ a₁) , unique (proofSetRef-ℕ r a₁))]
    p₁ : types (v ∖∖ [ n ] ∪ [(n , Unique (Ref-ℕ a₁) , _)]) ≡ types (v ∖∖ [ n ]) ∪ [(n , Unique (Ref-ℕ a₁))]
    p₁ = t-x∪y (v ∖∖ [ n ]) _
    p₂ : types (v ∖∖ [ n ]) ∪ [(n , Unique (Ref-ℕ a₁))] ≡ types v ∖∖ [ n ] ∪ [(n , Unique (Ref-ℕ a₁))]
    p₂ = ≡-cong (λ x → x ∪ [(n , Unique (Ref-ℕ a₁))]) (t-x∖y v [ n ])

{-
readHandle : (h n : String) {h≢!n : h s-≢! n} →
    Transformer ([(h , Unique Handle)] , nr-[a]) ((h , Unique Handle) ∷ [(n , Pure String)] , (x≢y⇒x∉l⇒x∉y∷l (s-≢!⇒≢? h≢!n) λ()) ∷ nr-[a])
readHandle h n v nr-v h⊆v _ = w , ≋-trans p₁ (≋-trans p₂ p₃) where
    r : Pure String
    r = pure ∘ readHandleNative ∘ Unique.get ∘ getBySignature ∘ h⊆v $ here refl
    w = v ∪ [(n , Pure String , r)]
    p₁ : types (v ∪ [(n , Pure String , r)]) ≋ types v ∪ [(n , Pure String)]
    p₁ = ≡⇒≋ $ t-x∪y v [(n , Pure String , r)]
    p₂ : types v ∪ [(n , Pure String)] ≋ (types v ∖∖ [ h ] ∪ [(h , Unique Handle)]) ∪ [(n , Pure String)]
    p₂ = x≋x̀⇒x∪y≋x̀∪y (≋-trans g₁ g₂) [(n , Pure String)] where
        g₁ : types v ≋ [(h , Unique Handle)] ∪ types v ∖∖ [ h ]
        g₁ = t₁⊆t₂⇒t₂≋t₁∪t₂∖nt₁ nr-[a] (nr-x⇒nr-t-x nr-v) h⊆v
        g₂ : [(h , Unique Handle)] ∪ types v ∖∖ [ h ] ≋ types v ∖∖ [ h ] ∪ [(h , Unique Handle)]
        g₂ = ∪-sym [(h , Unique Handle)] (types v ∖∖ [ h ])
    p₃ : (types v ∖∖ [ h ] ∪ [(h , Unique Handle)]) ∪ [(n , Pure String)] ≋ types v ∖∖ [ h ] ∪ ((h , Unique Handle) ∷ [(n , Pure String)])
    p₃ = ≡⇒≋ $ ∪-assoc (types v ∖∖ [ h ]) [(h , Unique Handle)] [(n , Pure String)]

closeHandle : (h : String) → Transformer! [(h , Unique Handle)] []
closeHandle h v nr-v h⊆v _ = w , ≡⇒≋ p where
    u = {-force-} closeHandleNative ∘ Unique.get ∘ getBySignature ∘ h⊆v $ here refl
    w = v ∖∖ [ h ]
    p : types (v ∖∖ [ h ]) ≡ types v ∖∖ [ h ] ∪ []
    p = ≡-trans (t-x∖y v [ h ]) (≡-sym $ x∪[]≡x (types v ∖∖ [ h ]))
-}

{-
proofGetRef-ℕ : {a : ℕ} → Ref-ℕ a → Exact a
proofGetRef-ℕ (r , p) = ≡-elim′ Exact p (exact $ nativeGetRef-ℕ r)

proofAddRef-ℕ : {a₁ a₂ : ℕ} → Ref-ℕ a₁ → Ref-ℕ a₂ → Ref-ℕ (a₁ + a₂)
proofAddRef-ℕ (r₁ , _) (r₂ , _) = nativeAddRef-ℕ r₁ r₂ , trustMe

proofFreeRef-ℕ : {a : ℕ} → Ref-ℕ a → Unit
proofFreeRef-ℕ (r , _) = nativeFreeRef-ℕ r
-}