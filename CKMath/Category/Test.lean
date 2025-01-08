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

variable (A : OA → OA → Sort v_A) (B : OB → OB → Sort v_B)
/-- The basic data of a `Functor`, consisting of a map between the arrows of a category. -/
@[ext]
structure Functor [𝓐 : Category A] [𝓑 : Category B] where
  /-- A map from objects of A to objects of B. -/
  obj : OA → OB
  /-- A map from maps in A to maps on the corresponding objects in B. -/
  map : A x y → B (obj x) (obj y)
  /-- The functor respects identity. -/
  map_id : @map x x 𝓐.id = 𝓑.id
  /-- The functor respects composition. -/
  map_comp : map (f ≫ g) = map f ≫ map g

end

namespace Functor

variable
  {A : OA → OA → Sort v_A}
  {B : OB → OB → Sort v_B}
  {C : OC → OC → Sort v_C}
  {C : OD → OD → Sort v_D}
  [𝓐 : Category A]
  [𝓑 : Category B]
  [𝓒 : Category C]
  [𝓓 : Category D]

def id : Functor A A where
  obj x := x
  map f := f
  map_id := by intros ; trivial
  map_comp := by intros ; trivial

def comp (F : Functor A B) (G : Functor B C) : Functor A C where
  obj := G.obj ∘ F.obj
  map := G.map ∘ F.map
  map_id := by simp [F.map_id, G.map_id]
  map_comp := by simp [F.map_comp, G.map_comp]

@[simp]
def pre_id {F : Functor A B} : id.comp F = F := by trivial

@[simp]
def post_id {F : Functor A B} : F.comp id = F := by trivial

@[simp]
def comp_assoc
  {F : Functor A B}
  {G : Functor B C}
  {H : Functor C D} :
  (F.comp G).comp H = F.comp (G.comp H) := by trivial

end Functor

section

variable {A : OA → OA → Sort v_A} {B : OB → OB → Sort v_B}
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

section whisker

variable {A : OA → OA → Sort v_A} {B : OB → OB → Sort v_B} {C : OC → OC → Sort v_C}
variable [𝓐 : Category A] [𝓑 : Category B] [𝓒 : Category C]

def whisker_pre
  (H : Functor B C) :
  Functor
  (NaturalTransformation (A := A) (B := B))
  (NaturalTransformation (A := A) (B := C)) where
  obj F := F.comp H
  map {F G} α := {
    on x := H.map (α.on x)
    natural := by
      intros
      simp [Functor.comp, ←H.map_comp, α.natural]
  }
  map_id := by
    intros
    ext
    simp only [Struct.id, NaturalTransformation.id_on, H.map_id]
  map_comp := by
    intros
    ext
    simp only [NaturalTransformation.comp_on, H.map_comp]

def whisker_post
  (H : Functor A B) :
  Functor
  (NaturalTransformation (A := B) (B := C))
  (NaturalTransformation (A := A) (B := C)) where
  obj F := H.comp F
  map {F G} α := {
    on x := α.on (H.obj x)
    natural := by
      intros
      simp [Functor.comp, α.natural]
  }
  map_id := by
    intros
    ext
    simp only [Struct.id, NaturalTransformation.id_on]
  map_comp := by
    intros
    ext
    simp only [NaturalTransformation.comp_on]

end whisker

end

end Category
