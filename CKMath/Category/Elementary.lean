/-
! This module should contain definitions for elementary categories, including the category of functions.
-/

import CKMath.Category.Definition

namespace Category

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

namespace Fun

@[simp]
def comp_apply {f : Fun A B} {g : Fun B C} {x : A} : (f ≫ g) x = g (f x) := by
  trivial

end Fun

section product

/-
! In this section, we define the product of two categories.
!
! This is more convoluted by having morphism focused library instead of an object-focused one.
! Rather than being able to define a category on `A × B`, we instead have to define the category
! on the morphisms of that category, which don't have a neatly pre-existing struct.
! Hence, the introduction of `BiMorphism`.
-/

/-- In essence, this is just two morphisms, one in each category. -/
@[ext]
structure BiMorphism
  (A : OA → OA → Sort v_A)
  (B : OB → OB → Sort v_B)
  (X : OA ×' OB)
  (Y : OA ×' OB)
where
  fst : A X.fst Y.fst
  snd : B X.snd Y.snd

infixr:100 " ⨂ " => BiMorphism

/-- A category structure on `A ⨂ B` which is compatible with the underlying categories.

There's a natural way of turning `A ⨂ B` into the morphisms of a category, which behaves
particularly nicely pointwise. This class captures that this category is being used,
allowing us to do reasoning beyond that of a plain category.

This is a bit of a "Lean hack" allowing us to assume that the category instance for
`A ⨂ B` has particular properties relating it to `A` and `B` individually.
-/
class BiCategory
  (A : OA → OA → Sort v_A)
  (B : OB → OB → Sort v_B)
  [𝓐 : Category A]
  [𝓑 : Category B]
  extends @Category _ (A ⨂ B) where
  bi_compat_id {x} : @id x = ⟨𝓐.id, 𝓑.id⟩
  bi_compat_comp
    {f : (A ⨂ B) x y}
    {g : (A ⨂ B) y z} :
    (f ≫ g) = ⟨f.fst ≫ g.fst, f.snd ≫ g.snd⟩

namespace BiMorphism

section

variable {A : OA → OA → Sort v_A} {B : OB → OB → Sort v_B}
variable [𝓐 : Category A] [𝓑 : Category B]

instance bicategory : BiCategory A B where
  id := ⟨𝓐.id, 𝓑.id⟩
  comp := fun ⟨f0, g0⟩ ⟨f1, g1⟩ => ⟨f0 ≫ f1, g0 ≫ g1⟩
  bi_compat_id := by
    intros
    trivial
  bi_compat_comp := by
    intros
    trivial
  pre_id := by
    intros
    simp only [𝓐.pre_id, 𝓑.pre_id]
  post_id := by
    intros
    simp only [𝓐.post_id, 𝓑.post_id]
  comp_assoc := by
    intros
    simp only [𝓐.comp_assoc, 𝓑.comp_assoc]
end

end BiMorphism

end product

section opposites

/-- The opposite of a given type of morphisms, i.e. morphisms in the reverse direction.

We define this as an opaque struct for better wieldiness.
 -/
@[ext]
structure Op (A : O_A → O_A → Sort v_A) (x y : O_A) where
  unop : A y x

namespace Op

variable {A : O_A → O_A → Sort v_A}

/-- A morphism can be treated as an opposite morphism, with the direction reversed. -/
def op (f : A x y) : (Op A) y x where
  unop := f

/-- To show that two opposite morphisms are the same, show that the underlying morphisms are. -/
@[simp]
theorem eq_iff_unop_eq (f g : (Op A) x y) : f = g ↔ f.unop = g.unop := by
  constructor
  . intro h
    rw [h]
  . intro h
    ext
    exact h

@[simp]
theorem op_unop (f : A x y) : (op f).unop = f := by trivial
section

variable [𝓐 : Category.Struct A]


/-- The category of opposites.

Because of our morphism centric approach, rather than looking at "the opposite category",
we instead look at "the category of opposite morphisms".
-/
instance categoryStruct : Category.Struct (Op A) where
  id := op 𝓐.id
  comp f g := op (g.unop ≫ f.unop)


/-- The opposite identity is in fact just the identity. -/
@[simp]
theorem unop_id_eq_id : unop (@categoryStruct.id x) = @𝓐.id x := by trivial

/-- Composing two opposite morphisms is just backwards composition. -/
@[simp]
theorem unop_comp_eq_comp_unop
  (f : (Op A) x y)
  (g : (Op A) y z) :
  (f ≫ g).unop = g.unop ≫ f.unop := by
  trivial

end

section

variable [𝓐 : Category A]

/-- Naturally, opposite morphisms form a category, if the underlying morphisms do. -/
instance category : Category (Op A) where
  pre_id := by
    intros
    simp only [eq_iff_unop_eq, unop_comp_eq_comp_unop, unop_id_eq_id, 𝓐.post_id]
  post_id := by
    intros
    simp only [eq_iff_unop_eq, unop_comp_eq_comp_unop, unop_id_eq_id, 𝓐.pre_id]
  comp_assoc := by
    intros
    simp only [eq_iff_unop_eq, unop_comp_eq_comp_unop, 𝓐.comp_assoc]

end

end Op

end opposites

end Category
