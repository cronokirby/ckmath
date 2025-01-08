/-- The basic data of a `Category`, without the corresponding laws.

This can be useful, allowing us to first define the data of a category,
giving us a composition operator, before then proving that it behaves correctly.
-/
class Category.Struct {O : Sort u} (Mor : O → O → Sort v) where
  /-- We require a particular morphism for any object, acting as the identity. -/
  id : Mor X X
  /-- We choose to compose arrows from left to right, binding to the right. -/
  comp : Mor A B → Mor B C → Mor A C

/-- We define `≫` as a convenient notation for composition of morphisms. -/
infixr:80 " ≫ " => Category.Struct.comp

class Category {O : Sort u} (Mor : O → O → Sort v) extends @Category.Struct O Mor where
  pre_id (f : Mor A B) : id ≫ f = f
  post_id (f : Mor A B) : f ≫ id = f
  comp_assoc (f : Mor A B) (g : Mor B C) (h : Mor C D) : (f ≫ g) ≫ h = f ≫ (g ≫ h)

/-- A synonym for `->`, acting as a carrier for the standard category of Sets.

Think of `Fun A B` as analogous to the textbook "Set(A, B)".
-/
abbrev Fun (A B : Sort u) := A → B

/-- Naturally, we can form a category of types (in a given universe) and functions between them.

For `Type`, we get the usual category of sets.

For `Prop`, we instead get the category of propositions and implications.
-/
instance Fun.category : Category Fun where
  id := id
  comp f g := g ∘ f
  pre_id := by intros ; rfl
  post_id := by intros ; rfl
  comp_assoc := by intros ; rfl
