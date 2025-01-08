/-- The basic data of a `Category`, without the corresponding laws.

This can be useful, allowing us to first define the data of a category,
giving us a composition operator, before then proving that it behaves correctly.
-/
class Category.Struct {O : Sort u} (Mor : O → O → Sort v) where
  /-- We require a particular morphism for any object, acting as the identity. -/
  id : Mor x x
  /-- We choose to compose arrows from left to right, binding to the right. -/
  comp : Mor a b → Mor b c → Mor a c

/-- We define `≫` as a convenient notation for composition of morphisms. -/
infixr:80 " ≫ " => Category.Struct.comp

class Category {O : Sort u} (Mor : O → O → Sort v) extends @Category.Struct O Mor where
  pre_id : id ≫ f = f
  post_id : f ≫ id = f
  comp_assoc {f : Mor a b} {g : Mor b c} {h : Mor c d} : (f ≫ g) ≫ h = f ≫ (g ≫ h)

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

namespace Category
-- Defining `Functor`, `Functor.Struct`
section

variable (A : OA → OA → Sort v) (B : OB → OB → Sort v)

/-- The basic data of a `Functor`, consisting of a map between the arrows of a category. -/
structure Functor.Struct [𝓐 : Category.Struct A] [𝓑 : Category.Struct B] where
  /-- A map from objects of A to objects of B. -/
  obj : OA → OB
  /-- A map from maps in A to maps on the corresponding objects in B. -/
  map : A x y → B (obj x) (obj y)

/-- Additionally, a functor is a *structure-preserving* map between categories. -/
structure Functor [𝓐 : Category A] [𝓑 : Category B] extends Functor.Struct A B where
  map_id : @map x x 𝓐.id = 𝓑.id
  map_comp : map (f ≫ g) = map f ≫ map g

end

end Category
