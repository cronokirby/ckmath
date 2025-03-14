/-
! This module should contain definitions for elementary categories, including the category of functions.
-/

import CKMath.Category.Definition

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

infixr:90 " ⨂ " => BiMorphism

namespace BiMorphism

section

variable {A : OA → OA → Sort v_A} {B : OB → OB → Sort v_B}
variable [𝓐 : Category.Struct A] [𝓑 : Category.Struct B]

/-- `BiMorphism`s have the structure of a category, with pointwise operations. -/
instance categoryStruct : Category.Struct (A ⨂ B) where
  id := ⟨𝓐.id, 𝓑.id⟩
  comp := fun ⟨f0, g0⟩ ⟨f1, g1⟩ => ⟨f0 ≫ f1, g0 ≫ g1⟩

@[simp]
def id_fst : (@Category.Struct.id _ (A ⨂ B) categoryStruct ⟨x, y⟩).fst = 𝓐.id := by
  trivial

@[simp]
def id_snd : (@Category.Struct.id _ (A ⨂ B) categoryStruct ⟨x, y⟩).snd = 𝓑.id := by
  trivial

@[simp]
def comp_fst
  {f : (A ⨂ B) x y}
  {g : (A ⨂ B) y z} :
  (f ≫ g).fst = f.fst ≫ g.fst := by
  constructor

@[simp]
def comp_snd
  {f : (A ⨂ B) x y}
  {g : (A ⨂ B) y z} :
  (f ≫ g).snd = f.snd ≫ g.snd := by
  constructor
end

section

variable [𝓐 : Category A] [𝓑 : Category B]

/-- As one might expect, if both constituents are categories, they form a joint category of bimorphisms. -/
instance category : Category (A ⨂ B) where
  pre_id := by
    intros
    ext
    . rw [comp_fst, id_fst, 𝓐.pre_id]
    . rw [comp_snd, id_snd, 𝓑.pre_id]
  post_id := by
    intros
    ext
    . rw [comp_fst, id_fst, 𝓐.post_id]
    . rw [comp_snd, id_snd, 𝓑.post_id]
  comp_assoc := by
    intros
    ext
    . simp only [comp_fst, 𝓐.comp_assoc]
    . simp only [comp_snd, 𝓑.comp_assoc]
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
