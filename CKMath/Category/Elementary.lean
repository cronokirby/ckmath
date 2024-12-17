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

/-- A carrier for the opposite of a category. -/
structure Opposite (α) where
  unop : α

/-- Give a category, explicitly construct the opposite category.

This provides a way to get the canonical instance of the opposite category,
allowing us to easily use the fact that we've used the standard instance in proving things.

This allows us to lean on opposites when defining categorical constructs.
-/
def Category.Op(C : Category O) : Category (Opposite O) := {
  Mor (A B) := C.Mor B.unop A.unop,
  id := C.id,
  comp (f g) := C.comp g f,
  pre_id := by
    simp [C.post_id]
  post_id := by
    simp [C.pre_id]
  comp_assoc := by
    simp [C.comp_assoc]
}

/-- The canonical instance for the opposite category. -/
instance instCategoryOpposite [C : Category O] : Category (Opposite O) := C.Op
