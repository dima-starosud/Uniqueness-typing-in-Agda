module HandleAPI where

open import Values public
open import Context
open import Transformer public
open import Data.List public using (List; []; _∷_; [_])

{-
postulate
    _seq_ : ∀ {a b} {A : Set a} {B : Set b} → A → B → B
    Handle : Set
    openHandleNative : String → Handle
    readHandleNative : Handle → String
    closeHandleNative : Handle → Unit
-}

_seq_ : ∀ {a b} {A : Set a} {B : Set b} → A → B → B
a seq b = b

record Handle : Set where
    field get : String

openHandleNative : String → Handle
openHandleNative name = record {get = "some data"}

readHandleNative : Handle → String
readHandleNative h = Handle.get h

closeHandleNative : Handle → Unit
closeHandleNative h = unit

openHandle : (name : String) (h : String) → Transformer! [] [(h , Unique Handle)]
openHandle name h ctx nr-v []⊆v nr-v∪n = context w , (≡⇒≋ $ ≡-trans p₁ p₂) where
    v = Context.get ctx
    w = v ∪ [(h , Unique Handle , unique (openHandleNative name))]
    p₁ : types (v ∪ [(h , Unique Handle , _)]) ≡ types v ∪ [(h , Unique Handle)]
    p₁ = t-x∪y v [(h , Unique Handle , _)]
    p₂ : types v ∪ [(h , Unique Handle)] ≡ types v ∖∖ [] ∪ [(h , Unique Handle)]
    p₂ = ≡-cong (λ x → x ∪ [(h , Unique Handle)]) (≡-sym $ t∖[]≡t $ types v)

readHandle : (h n : String) {h≢!n : h s-≢! n} →
    Transformer ([(h , Unique Handle)] , nr-[a]) ((h , Unique Handle) ∷ [(n , Pure String)] , (x≢y⇒x∉l⇒x∉y∷l (s-≢!⇒≢? h≢!n) λ()) ∷ nr-[a])
readHandle h n ctx nr-v h⊆v _ = context w , ≋-trans p₁ (≋-trans p₂ p₃) where
    v = Context.get ctx
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
closeHandle h ctx nr-v h⊆v _ = u seq (context w , ≡⇒≋ p) where
    v = Context.get ctx
    u = closeHandleNative ∘ Unique.get ∘ getBySignature ∘ h⊆v $ here refl
    w = v ∖∖ [ h ]
    p : types (v ∖∖ [ h ]) ≡ types v ∖∖ [ h ] ∪ []
    p = ≡-trans (t-x∖y v [ h ]) (≡-sym $ x∪[]≡x (types v ∖∖ [ h ]))
