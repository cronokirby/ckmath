import CKMath.Category.Definition
import CKMath.Category.Elementary
import CKMath.Category.Functor

namespace Category

/-- Represents a bifunctor from two categories to a target one. -/
def BiFunctor
  (A : OA → OA → Sort v_A)
  (B : OB → OB → Sort v_B)
  (C : OC → OC → Sort v_C)
  [Category A]
  [Category B]
  [Category C] :=
  (A ⨂ B) ⥤ C

end Category
