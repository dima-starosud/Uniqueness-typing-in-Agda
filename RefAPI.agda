module RefAPI where

open import Context hiding (_:=_)

open import Function
open import Data.Nat
open import Data.String
open import Data.Vec
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
    nativeRef-New-ℕ : (init : ℕ) → nativeRef ℕ
    nativeRef-Set-ℕ : ℕ → nativeRef ℕ
    nativeRef-Get-ℕ : nativeRef ℕ → ℕ
    nativeRef-Add-ℕ : nativeRef ℕ → nativeRef ℕ → nativeRef ℕ
    nativeRef-Free-ℕ : nativeRef ℕ → Unit

data Exact {ℓ} {A : Set ℓ} : A → Set ℓ where
    exact : ∀ a → Exact a

proofRef : {A : Set} (a : A) → Set
proofRef {A = A} _ = nativeRef A

proofRef-New-ℕ : (a : ℕ) → proofRef a
proofRef-New-ℕ = nativeRef-New-ℕ

proofRef-Set-ℕ : (a : ℕ) → proofRef a
proofRef-Set-ℕ = nativeRef-Set-ℕ

proofRef-Get-ℕ : {a : ℕ} → proofRef a → Exact a
proofRef-Get-ℕ {a = a} r = ≡-elim′ Exact à≡a (exact à) where
    à = nativeRef-Get-ℕ r
    à≡a : à ≡ a
    à≡a = trustMe

proofRef-Add-ℕ : {a₁ a₂ : ℕ} → proofRef a₁ → proofRef a₂ → proofRef (a₁ + a₂)
proofRef-Add-ℕ = nativeRef-Add-ℕ

proofRef-Free-ℕ : {a : ℕ} → proofRef a → Unit
proofRef-Free-ℕ = nativeRef-Free-ℕ

{-
data Bit : Set where
    T F : Bit

Bits : Set
Bits = ∃ λ n → Vec Bit n

postulate
    nativeRef : (A : Set) → Set
    nativeNewRef : {A : Set} (serialize : A → Bits) (deserialize : Bits → A) (a : A) → nativeRef A
    nativeUpdateRef : {A : Set} → nativeRef A → (f : A → A) → nativeRef A
    nativeExtractRef : {A : Set} → nativeRef A → A
    nativeFreeRef : {A : Set} → nativeRef A → Unit

data Exact {ℓ} {A : Set ℓ} : A → Set ℓ where
    exact : ∀ a → Exact a

proofRef : {A : Set} (a : A) → Set
proofRef {A = A} _ = nativeRef A

proofNewRef : {A : Set} (a : A) → proofRef a
proofNewRef = nativeNewRef

proofUpdateRef : {A : Set} {a : A} → proofRef a → (f : A → A) → proofRef (f a)
proofUpdateRef = nativeUpdateRef

proofExtractRef : {A : Set} {a : A} → proofRef a → Exact a
proofExtractRef {a = a} _ = exact a

proofFreeRef : {A : Set} {a : A} → proofRef a → Unit
proofFreeRef = nativeFreeRef
-}
{-
postulate
    Ref : {A : Set} (a : A) → Set
    newRef : {A : Set} (a : A) → Ref a
    updateRef : {A : Set} {a : A} → Ref a → (f : A → A) → Ref (f a)
    extractRef : {A : Set} {a : A} → Ref a → Exact a
    freeRef : {A : Set} {a : A} → Ref a → Unit

newRef : ∀ a n → Transformer! [] [(n , Unique (Ref a))]
newRef a n v nr-v []⊆v nr-v∪n = w , (≡⇒≋ $ ≡-trans p₁ p₂) where
    w = v ∪ [(n , Unique (Ref a) , unique (newRef a))]
    p₁ : types (v ∪ [(n , Unique (Ref a) , _)]) ≡ types v ∪ [(n , Unique (Ref a))]
    p₁ = t-x∪y v [(n , Unique (Ref a) , _)]
    p₂ : types v ∪ [(n , Unique (Ref a))] ≡ types v ∖∖ [] ∪ [(n , Unique (Ref a))]
    p₂ = ≡-cong (λ x → x ∪ [(n , Unique (Ref a))]) (≡-sym $ t∖[]≡t $ types v)
-}

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

{-
Doesn't work without type constraint:
    "An internal error has occurred. Please report this as a bug.
    Location of the error: src/full/Agda/TypeChecking/Substitute.hs:607"
I will try it later with the latest version of Agda.
-}

getHandle′ : ∀ _ h → Transformer! [] [ (h , Unique Handle) ]
getHandle′ = getHandle

tr = "h" := getHandle′ "handle" ⇒⟦ refl ⟧⇒
     "s" := readHandle "h"      ⇒⟦ refl ⟧⇒
     closeHandle "h"

p : extract tr ≡ "handle"
p = refl
-}