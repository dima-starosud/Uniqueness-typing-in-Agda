module HandleAPITest where

open import HandleAPI
{-Doesn't work without type constraint:
    "An internal error has occurred. Please report this as a bug.
    Location of the error: src/full/Agda/TypeChecking/Substitute.hs:607"
  I will try it later with the latest version of Agda.-}

openHandle′ : ∀ _ h → Transformer! [] [(h , Unique Handle)]
openHandle′ = openHandle

tr = "h" := openHandle′ "file" ⇒⟦ refl ⟧⇒
     "s" := readHandle "h"     ⇒⟦ refl ⟧⇒
     closeHandle "h"

p : extract tr ≡ "some data"
p = refl
