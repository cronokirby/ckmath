import CKMath.Category.Definition
import CKMath.Category.Elementary
import CKMath.Category.Functor

namespace Category

namespace BiFunctor

variable {A : OA → OA → Sort v_A}
variable {B : OB → OB → Sort v_B}
variable {C : OC → OC → Sort v_C}
variable [𝓐 : Category A] [𝓑 : Category B] [𝓒 : Category C]
variable [𝓐x𝓑 : BiCategory A B]

/-- A bifunctor acts on a pair of identities by producing the identity. -/
def map_id (F : (A ⨂ B) ⥤ C) : F.map ⟨𝓐.id, 𝓑.id⟩ = @𝓒.id (F.obj x) := by
  suffices ⟨𝓐.id, 𝓑.id⟩ = @𝓐x𝓑.id x by
    rw [this]
    exact F.map_id
  rw [𝓐x𝓑.bi_compat_id]

end BiFunctor

end Category
