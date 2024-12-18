import CKMath.Category.Definition
import CKMath.Category.Morphism

namespace Category

/-- A pseudo functor is a map between categories, which may be structure preserving.

This class exists to let us easily define functors incrementally, by giving their definition
before we're ready to prove properties.
-/
structure PseudoFunctor (C) [𝓒 : Category.Struct C] (D) [𝓓 : Category.Struct D] where
  obj : C → O
  map {A B : C} : 𝓒.Mor A B → 𝓓.Mor (obj A) (obj B)

/-- A functor is a structure preserving map between categories. -/
structure Functor (C) [𝓒 : Category C] (D) [𝓓 : Category D] extends PseudoFunctor C D where
  map_id {X : C} : @map X X 𝓒.id = 𝓓.id
  map_comp {X Y Z : C} {f : 𝓒.Mor X Y} {g : 𝓒.Mor Y Z}: map (f ≫ g) = map f ≫ map g

namespace Functor

variable [𝓒 : Category C] [𝓓 : Category D]

/-- Functors map isomorphisms to isomorphisms. -/
def map_iso (F : Functor C D) (i : A ≅ B) : 𝓓.Isomorphism (F.obj A) (F.obj B) := {
  out := F.map i.out,
  inv := F.map i.inv,
  pre_inv := by
    rw [←F.map_comp, i.pre_inv]
    exact F.map_id
  post_inv := by
    rw [←F.map_comp, i.post_inv]
    exact F.map_id
}

end Functor

end Category
