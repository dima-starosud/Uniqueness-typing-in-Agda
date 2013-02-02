module HandleAPITest where

open import HandleAPI

tr = "h" := openHandle "file" ⇒⟦ refl ⟧⇒
     "s" := readHandle "h"    ⇒⟦ refl ⟧⇒
     closeHandle "h"

p : extract tr ≡ "some data"
p = refl
