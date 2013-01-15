Uniqueness-typing-in-Agda
=========================

The main idea behind uniqueness types is context management.<br>
Consider next example:<br>

h = openHandle "name" -- 'h : Handle' is added to the context<br>
a = readData h<br>
close h               -- 'h' is removed from the context<br>
b = readData h        -- compiler should complain here: 'h is undefined' or something like this<br>

Another more important thing is changing of the properties of the objects:<br>

-- ptr - pointer to int<br>
-- p-1 - proof that value 1 is in memory, pointed by ptr<br>
ptr , p-1 = new int(1)<br>

-- p-5 - proof that value 5 is in memory, pointed by ptr<br>
p-5 = write ptr 5<br>

Without uniqueness types we would have two contradictory statements at one time,<br>
which would lead to inconsistency.<br>
So, when a new proof is obtained, the old one should be thrown away.<br>


IMPLEMENTATION (Context.agda)<br>
  Context is a polymorphic list of 3-elements-tuple (name, type, value):<br>
  Values : ∀ ℓ → Set (Level.suc ℓ)<br>
  Values ℓ = List (String × (Σ[ A ∶ Set ℓ ] A))<br>

  Transformer is used for building functions.<br>
  It takes values with all the necessary proofs, removes consumed objects and adds newly created.<br>
  Transformers are piped with creating a new transformer.<br>

EXAMPLES (HandleAPI.agda, RefAPI.agda)<br>
  --TODO: show<br>


QUESTIONS<br>
  --TODO: ask<br>

This prototype is a proof of concept and shouldn't be used as a base for further development.<br>
It is easier to rewrite it than to re-factor :)<br>

