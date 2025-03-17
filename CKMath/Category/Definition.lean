/-
! This module contains the basic definitions of what a `Category` actually is.
!
! This is intended to be kept minimal, since it is depended on everywhere else we use categories.
-/

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

section

variable {A : OA → OA → Sort v_A} [Category.Struct A]

/-- We provide an instance of transitivity for categories.

This is useful because some relations of interest form categories.
E.g. isomorphisms, equivalences, etc.
-/
instance Category.Struct.trans : Trans A A A where
  trans := comp

end
