/-- Sorts have an instance of this class when they have a Category structure.

This means that the members of this sort can be considered as *objects* in some
category, to which we can associate some other sort for the morphisms between these objects.
We also have, for each object, an identity morphism, and, for any two pairs of objects,
ways of composing the morphisms between them.

This does not yet contain any properties about these data: `Category O` has them instead.

Small categories will have `O : Type`, and large categories will have a large `O`.
For example: `Type : Type 1`.
-/
class Category.Struct (O : Sort u) where
  /-- Each pair of objects gets its own sort of morphism. -/
  Mor : O → O → Sort v
  /-- Each such sort has a distinguished identity morphism. -/
  id : Mor A A
  /-- We can compose morphisms to link many objects together. -/
  comp : Mor A B → Mor B C → Mor A C

infixr:80 " ≫ " => Category.Struct.comp

/-- A category has the structure of a category—objects, morphisms, identities, composition—and laws.
-/
class Category (O : Sort u) extends Category.Struct O where
  /-- The identity does nothing before a morphism. -/
  pre_id (f : Mor A B) : id ≫ f = f
  /-- The identity does nothing after a morphism-/
  post_id (f : Mor A B) : f ≫ id = f
  /-- We can compose morphisms without regard to the grouping. -/
  comp_assoc (f : Mor A B) (g : Mor B C) (h : Mor C D) :
    f ≫ (g ≫ h) = (f ≫ g) ≫ h

-- Some basic simplification lemmas from the definition.
namespace Category

variable [𝓒 : Category O]

@[simp]
theorem pre_id_simp {A B : O} {f : 𝓒.Mor A B} : 𝓒.id ≫ f = f := 𝓒.pre_id f

@[simp]
theorem post_id_simp {A B : O} {f : 𝓒.Mor A B} : f ≫ 𝓒.id = f := 𝓒.post_id f

@[simp]
theorem comp_assoc_simp
  {A B C D : O} {f : 𝓒.Mor A B} {g : 𝓒.Mor B C} {h : 𝓒.Mor C D}
  : f ≫ (g ≫ h) = (f ≫ g) ≫ h
  := 𝓒.comp_assoc f g h

end Category
