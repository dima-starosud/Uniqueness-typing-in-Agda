<pre>
<h2>Uniqueness-typing-in-Agda</h2>

The main idea behind uniqueness types is context management.
Consider next example:

h = openHandle "name" -- 'h : Handle' is added to the context
a = readData h
close h               -- 'h' is removed from the context
b = readData h        -- compiler should complain here: 'h is undefined' or something like this

Another more important thing is changing of the properties of the objects:

-- ptr - pointer to int
-- p-1 - proof that value 1 is in memory, pointed by ptr
ptr , p-1 = new int(1)

-- p-5 - proof that value 5 is in memory, pointed by ptr
p-5 = write ptr 5

Without uniqueness types we would have two contradictory statements at one time,
which would lead to inconsistency.
So, when a new proof is obtained, the old one should be thrown away.


IMPLEMENTATION (Context.agda)
  Context is a polymorphic list of 3-elements-tuple (name, type, value):
  Values : ∀ ℓ → Set (Level.suc ℓ)
  Values ℓ = List (String × (Σ[ A ∶ Set ℓ ] A))

  Transformer is used for building functions.
  It takes values with all the necessary proofs, removes consumed objects and adds newly created.
  Transformers are piped with creating a new transformer.

EXAMPLES (HandleAPI.agda, RefAPI.agda)
  --TODO: show


QUESTIONS
  --TODO: ask

This prototype is a proof of concept and shouldn't be used as a base for further development.
It is easier to rewrite it than to re-factor :)

</pre>
