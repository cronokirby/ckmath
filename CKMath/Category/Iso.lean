import CKMath.Category.Definition
import CKMath.Category.Functor

namespace Category

variable {OA : Sort u_A}

/-- Represents an isomorphism in some category.

An isomorphism is a morphism with a proper inverse.
-/
@[ext]
structure Iso (A : OA → OA → Sort v_A) [𝓐 : Category A] (x y : OA) where
  out : A x y
  inv : A y x
  inv_pre : inv ≫ out = 𝓐.id
  inv_post : out ≫ inv = 𝓐.id

namespace Iso

variable {A : OA → OA → Sort v_A}
variable [𝓐 : Category A]

/-- When the main function of an isomorphism is equal, the inverses are also equal. -/
def out_eq_implies_inv_eq {f g : Iso A x y} : f.out = g.out → f.inv = g.inv := by
  intro h
  calc
  _ = f.inv ≫ 𝓐.id := by rw [𝓐.post_id]
  _ = f.inv ≫ (g.out ≫ g.inv) := by rw [g.inv_post]
  _ = f.inv ≫ (f.out ≫ g.inv) := by rw [h]
  _ = g.inv := by rw [←𝓐.comp_assoc, f.inv_pre, 𝓐.pre_id]

/-- To compare isomorphisms, it suffices to compare the primary morphisms. -/
@[simp]
def eq_iff_out_eq {f g : Iso A x y} : f = g ↔ f.out = g.out := by
  constructor
  . intro h
    rw [h]
  . intro h
    ext
    . exact h
    . exact out_eq_implies_inv_eq h

/-- There's a natural isomorphism from an object to itself. -/
def id : Iso A x x where
  out := 𝓐.id
  inv := 𝓐.id
  inv_pre := 𝓐.pre_id
  inv_post := 𝓐.post_id

/-- We can compose isomorphisms as well. -/
def comp (f : Iso A X Y) (g : Iso A Y Z) : Iso A X Z where
  out := f.out ≫ g.out
  inv := g.inv ≫ f.inv
  inv_pre := by
    calc
    _ = g.inv ≫ (f.inv ≫ f.out) ≫ g.out := by simp only [𝓐.comp_assoc]
    _ = 𝓐.id := by rw [f.inv_pre, 𝓐.pre_id, g.inv_pre]
  inv_post := by
    calc
    _ = f.out ≫ (g.out ≫ g.inv) ≫ f.inv := by simp only [𝓐.comp_assoc]
    _ = 𝓐.id := by rw [g.inv_post, 𝓐.pre_id, f.inv_post]

instance categoryStruct : Category.Struct (Iso A) where
  id := id
  comp f g := f.comp g

@[simp]
def id_out {x : OA} : categoryStruct.id.out = 𝓐.id (x := x) := by trivial

@[simp]
def comp_out {f : Iso A x y} {g : Iso A y z} : (f ≫ g).out = f.out ≫ g.out := by trivial

/-- Isomorphisms assemble into a category. -/
instance category : Category (Iso A) where
  pre_id := by
    intros
    simp only [eq_iff_out_eq, comp_out, id_out, 𝓐.pre_id]
  post_id := by
    intros
    simp only [eq_iff_out_eq, comp_out, id_out, 𝓐.post_id]
  comp_assoc := by
    intros
    simp only [eq_iff_out_eq, comp_out, 𝓐.comp_assoc]

end Iso

/-- A short abbreviation for natural isomorphisms.

We define these as simply being isomorphisms in the category of natural transformations.

This immediately gives us the fact that they form a category, making this
a better definition.
-/
abbrev NatIso
  (A : OA → OA → Sort v_A)
  (B : OB → OB → Sort v_B)
  [𝓐 : Category A]
  [𝓑 : Category B]
  := Iso (Nat A B)

infixr:82 " ≅ " => NatIso _ _

end Category
