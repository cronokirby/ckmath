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
structure Functor [𝓐 : Category.Struct A] [𝓑 : Category.Struct B] where
  /-- A map from objects of A to objects of B. -/
  obj : OA → OB
  /-- A map from maps in A to maps on the corresponding objects in B. -/
  map : A x y → B (obj x) (obj y)

/-- Usually, we require the Functor to preserve structure, calling it "behaved".

In textbook category theory, all functors are behaved, and unbehaved functors might be called
"prefunctors" instead. It turns out that for many theorems and definitions the mapping
structure is all that's needed, which makes the well-behavedness useful to attach as a typeclass,
especially since there's only one instance of the proofs that the functor behaves well.
 -/
class Functor.Behaved [𝓐 : Category A] [𝓑 : Category B] (F : Functor A B) where
  map_id : @F.map x x 𝓐.id = 𝓑.id
  map_comp : F.map (f ≫ g) = F.map f ≫ F.map g

end

section

variable {A : OA → OA → Sort v} {B : OB → OB → Sort v}
variable [𝓐 : Category A] [𝓑 : Category B]

@[ext]
structure NaturalTransformation (F G : Functor A B) where
  on (x) : B (F.obj x) (G.obj x)
  natural {f : A x y} : on x ≫ G.map f = F.map f ≫ on y

infixr:81 " ⇒ " => NaturalTransformation

namespace NaturalTransformation

def id {F: Functor A B} : F ⇒ F where
  on _ := 𝓑.id
  natural := by
    intros
    rw [pre_id, post_id]

def comp {F G H : Functor A B} (α : F ⇒ G) (β : G ⇒ H) : F ⇒ H where
  on x := α.on x ≫ β.on x
  natural := by
    intros
    rw [comp_assoc, β.natural, ←comp_assoc, α.natural, comp_assoc]

instance categoryStruct : Category.Struct (O := Functor A B) NaturalTransformation where
  id := id
  comp := comp

@[simp]
theorem id_on {F : Functor A B} : (id (F := F)).on x = 𝓑.id := by trivial

@[simp]
theorem comp_on
  {F G H : Functor A B}
  {α : F ⇒ G}
  {β : G ⇒ H}
  {x} :
  (α ≫ β).on x = α.on x ≫ β.on x := by
    trivial

instance category : Category (O := Functor A B) NaturalTransformation where
  pre_id := by
    intros
    ext
    simp only [comp_on, Struct.id, id_on, pre_id]
  post_id := by
    intros
    ext
    simp only [comp_on, Struct.id, id_on, post_id]
  comp_assoc := by
    intros
    ext
    simp only [comp_on, comp_assoc]

end NaturalTransformation

end

end Category
