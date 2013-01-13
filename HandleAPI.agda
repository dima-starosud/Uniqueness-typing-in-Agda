module HandleAPI where

open import Context

open import Function
open import Data.String
open import Data.List
open import Data.List.Any
open import Data.Product
open import Data.Unit using (Unit; unit; ⊤)
open import Relation.Binary.Core

open import Relation.Binary.PropositionalEquality hiding ([_]) renaming (cong to ≡-cong; cong₂ to ≡-cong₂)
open import Relation.Binary.PropositionalEquality.Core renaming (sym to ≡-sym; trans to ≡-trans)

{-
postulate
    Handle : Set
    getHandleNative : String → Handle
    readHandleNative : Handle → String
    closeHandleNative : Handle → Unit
-}

record Handle : Set where
    field get : String

getHandleNative : String → Handle
getHandleNative s = record {get = s}

readHandleNative : Handle → String
readHandleNative h = Handle.get h

closeHandleNative : Handle → Unit
closeHandleNative _ = unit

getHandle : (name : String) (h : String) → Transformer! [] [(h , Unique Handle)]
getHandle name h v nr-v []⊆v nr-v∪n = w , (≡⇒≋ $ ≡-trans p₁ p₂) where
    w = v ∪ [(h , Unique Handle , unique (getHandleNative name))]
    p₁ : types (v ∪ [(h , Unique Handle , _)]) ≡ types v ∪ [(h , Unique Handle)]
    p₁ = t-x∪y v [(h , Unique Handle , _)]
    p₂ : types v ∪ [(h , Unique Handle)] ≡ types v ∖∖ [] ∪ [(h , Unique Handle)]
    p₂ = ≡-cong (λ x → x ∪ [(h , Unique Handle)]) (≡-sym $ t∖[]≡t $ types v)

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