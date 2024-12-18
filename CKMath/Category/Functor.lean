import CKMath.Category.Definition

namespace Category

variable [𝓒 : Category O_C] [𝓓 : Category O_D]

/-- A pseudo functor is a map between categories, which may be structure preserving.

This class exists to let us easily define functors incrementally, by giving their definition
before we're ready to prove properties.
-/
structure PseudoFunctor where
  obj : O_C → O_D
  map {A B : O_C} : 𝓒.Mor A B → 𝓓.Mor (obj A) (obj B)

/-- A functor is a structure preserving map between categories. -/
structure Functor extends @PseudoFunctor O_C O_D _ _ where
  map_id {A : O_C} : @map A A 𝓒.id = 𝓓.id
  map_comp {A B C : O_C} {f : 𝓒.Mor A B} {g : 𝓒.Mor B C}: map (f ≫ g) = map f ≫ map g

end Category
