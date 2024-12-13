/-
! This file defines some elementary categories which are useful in other places.
-/

import CKMath.Category.Definition


namespace Category

/-- A generalization of the category of types to apply to any sort.

The main reason for this generalization is to define the category of propositions,
but we also get wacky higher types for free as well.
-/
instance ofSort : Category (Sort u) where
  Mor (a : Sort u) (b : Sort u) := (a → b)
  id := fun (x) => x
  comp f g := g ∘ f
  pre_id := by
    intros
    rfl
  post_id := by
    intros
    rfl
  comp_assoc := by
    intros
    rfl

/-- The category whose objects are propositions, and whose morphisms are implications. -/
abbrev ofProp := ofSort.{0}

/-- The category whose objects are types, and whose morphisms are functions.

This is our version of `SET` in textbook category theory.
-/
abbrev ofType := ofSort.{1}

end Category
