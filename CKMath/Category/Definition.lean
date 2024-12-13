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
