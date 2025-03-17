import CKMath.Category.Definition
import CKMath.Category.Functor

namespace Category

variable {OA : Sort u_A}

/-- An inverse for a particular morphism composes with it to form the identity.

It's useful to separate out the inverse itself from a full isomorphism,
that way we can talk about a morphism with some structure having some property,
and then how the inverse might gain an analogous property.

This is useful e.g. to say that a natural transformation + inverse to the carrier
(without assuming naturality yet) is a natural isomorphism.
-/
@[ext]
structure Inverse
  {A : OA → OA → Sort v_A}
  [𝓐 : Category.Struct A]
  (f : A x y) where
  inv : A y x
  inv_pre : inv ≫ f = 𝓐.id
  inv_post : f ≫ inv = 𝓐.id

namespace Inverse

variable {A : OA → OA → Sort v_A}
variable [𝓐 : Category A]

/-- Any inverse is as good as any other! -/
def unique (f : A x y) (g0 g1 : Inverse f) : g0 = g1 := by
  ext
  calc
    _ = g0.inv := by rfl
    _ = g0.inv ≫ 𝓐.id := by rw [𝓐.post_id]
    _ = g0.inv ≫ f ≫ g1.inv := by rw [g1.inv_post]
    _ = (g0.inv ≫ f) ≫ g1.inv := by rw [𝓐.comp_assoc]
    _ = g1.inv := by rw [g0.inv_pre, 𝓐.pre_id]

/-- Inverses naturally compose. -/
def comp {f0 : A x y} {f1 : A y z} (g0 : Inverse f0) (g1 : Inverse f1) : Inverse (f0 ≫ f1) := {
  inv := g1.inv ≫ g0.inv,
  inv_pre := by
    calc
    _ = g1.inv ≫ (g0.inv ≫ f0) ≫ f1 := by simp only [𝓐.comp_assoc]
    _ = 𝓐.id := by rw [g0.inv_pre, 𝓐.pre_id, g1.inv_pre]
  inv_post := by
    calc
    _ = f0 ≫ (f1 ≫ g1.inv) ≫ g0.inv := by simp only [𝓐.comp_assoc]
    _ = 𝓐.id := by rw [g1.inv_post, 𝓐.pre_id, g0.inv_post]
}

end Inverse

/-- Represents an isomorphism in some category.

An isomorphism is a morphism with an inverse.
-/
@[ext]
structure Iso (A : OA → OA → Sort v_A) [𝓐 : Category.Struct A] (x y : OA) where
  out : A x y
  inv : Inverse out

namespace Iso

variable {A : OA → OA → Sort v_A}
variable [𝓐 : Category A]

/-- To compare isomorphisms, it suffices to compare the primary morphisms.

This is because any two inverses of a given morphism are equal.
-/
@[simp]
def eq_iff_out_eq {f g : Iso A x y} : f = g ↔ f.out = g.out := by
  constructor
  . intro h
    rw [h]
  . intro h
    ext
    . exact h
    . apply heq_of_eqRec_eq
      . apply Inverse.unique
      . rw [h]

/-- There's a natural isomorphism from an object to itself. -/
def id : Iso A x x where
  out := 𝓐.id
  inv := {
    inv := 𝓐.id,
    inv_pre := 𝓐.pre_id,
    inv_post := 𝓐.post_id
  }

/-- We can compose isomorphisms as well. -/
def comp (f : Iso A X Y) (g : Iso A Y Z) : Iso A X Z where
  out := f.out ≫ g.out
  inv := f.inv.comp g.inv

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

namespace NatIso

variable {A : OA → OA → Sort v_A}
variable {B : OB → OB → Sort v_B}
variable [𝓐 : Category A]
variable [𝓑 : Category B]

/-- Two functors that are equal are certainly isomorphic.

This turns out to be useful, because we have on-the-nose equality for
equations involving the identity functor, but want to work with isomorphisms
instead, usually.
-/
def from_eq {F : A ⥤ B} {G : A ⥤ B} (h_eq : F = G) : F ≅ G := by
  rw [h_eq]
  exact Iso.id

/-- Construct a natural isomorphism from a transformation and a bundle of inverses.

The key proof involved here is that naturality of the bundle of inverses follows simply
from the underlying transformation being natural.
-/
def from_inverse
  {F : A ⥤ B}
  {G : A ⥤ B}
  (φ : F ⇓ G)
  (inverse_on : (x : OA) → Inverse (φ.on x))
  : (F ≅ G)
  := {
    out := φ,
    inv := {
      inv := {
        on x := (inverse_on x).inv
        natural := by
          intro x y f
          calc
          _ = (inverse_on x).inv ≫ (F.map f ≫ φ.on y) ≫ (inverse_on y).inv := by
            rw [comp_assoc, (inverse_on y).inv_post, post_id]
          _ = (inverse_on x).inv ≫ (φ.on x ≫ G.map f) ≫ (inverse_on y).inv := by
            rw [φ.natural]
          _ = G.map f ≫ (inverse_on y).inv := by
            simp only [←comp_assoc, (inverse_on x).inv_pre, pre_id]
      },
      inv_pre := by
        apply Nat.eq_iff_on_eq.mpr
        intro x
        rw [Nat.comp_on, (inverse_on x).inv_pre]
        exact Nat.id_on
      inv_post := by
        apply Nat.eq_iff_on_eq.mpr
        intro x
        rw [Nat.comp_on, (inverse_on x).inv_post]
        exact Nat.id_on
    }
  }
end NatIso

end Category
