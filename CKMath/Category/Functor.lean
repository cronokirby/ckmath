/-
! Definitions related to functors and natural transformations.
-/
import CKMath.Category.Definition

namespace Category

/-- The basic data of a `Functor`, consisting of a map between the arrows of a category. -/
@[ext]
structure Functor
  (A : OA → OA → Sort v_A)
  (B : OB → OB → Sort v_B)
  [𝓐 : Category A]
  [𝓑 : Category B] where
  /-- A map from objects of A to objects of B. -/
  obj : OA → OB
  /-- A map from maps in A to maps on the corresponding objects in B. -/
  map : A x y → B (obj x) (obj y)
  /-- The functor respects identity. -/
  map_id : @map x x 𝓐.id = 𝓑.id
  /-- The functor respects composition. -/
  map_comp : map (f ≫ g) = map f ≫ map g

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

@[simp]
theorem eq_iff_on_eq {F G : Functor A B} {α β : F ⇒ G} : α = β ↔ ∀ x, α.on x = β.on x := by
  apply Iff.intro
  . intro h _
    rw [h]
  . intro h
    ext
    rw [h]

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

@[simp]
def whisker_pre_on
  {H : Functor B C}
  {F0 F1 : Functor A B}
  {α : F0 ⇒ F1}
  {x} :
  ((whisker_pre H).map α).on x = H.map (α.on x) := by rfl

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

@[simp]
def whisker_post_on
  {H : Functor A B}
  {F0 F1 : Functor B C}
  {α : F0 ⇒ F1}
  {x} :
  ((whisker_post H).map α).on x = α.on (H.obj x) := by rfl

end whisker

section hcomp

namespace NaturalTransformation

variable {A : OA → OA → Sort v_A} {B : OB → OB → Sort v_B} {C : OC → OC → Sort v_C}
variable [𝓐 : Category A] [𝓑 : Category B] [𝓒 : Category C]
variable {F0 F1 F2 : Functor A B} {G0 G1 G2 : Functor B C}

section

variable (α : F0 ⇒ F1) (β : G0 ⇒ G1)

abbrev hcomp_post_pre : (F0.comp G0) ⇒ (F1.comp G1) :=
  (whisker_post F0).map β ≫ (whisker_pre G1).map α

abbrev hcomp_pre_post : (F0.comp G0) ⇒ (F1.comp G1) :=
  (whisker_pre G0).map α ≫ (whisker_post F1).map β

theorem hcomp_pre_post_eq_post_pre : hcomp_pre_post α β = hcomp_post_pre α β := by
  -- output of `simp? [β.natural]`.
  simp only [eq_iff_on_eq, comp_on, whisker_pre_on, whisker_post_on, β.natural, implies_true]

def NaturalTransformation.hcomp : (F0.comp G0) ⇒ (F1.comp G1) := hcomp_post_pre α β

end

end NaturalTransformation

end hcomp

end

end Category
