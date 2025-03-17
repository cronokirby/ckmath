import CKMath.Category.Definition
import CKMath.Category.Functor
import CKMath.Category.Iso

namespace Category

/-- Represents an equivalence between two categories.

This shows that the two categories are essentially the same.
-/
structure Equivalence
  (A : OA → OA → Sort v_A)
  (B : OB → OB → Sort v_B)
  [Category A]
  [Category B]
where
  fwd : A ⥤ B
  bwd : B ⥤ A
  fwd_bwd_iso_id : (fwd ⋙ bwd) ≅ Functor.id
  bwd_fwd_iso_id : (bwd ⋙ fwd) ≅ Functor.id

infixr:82 " ≅ " => Equivalence

namespace Equivalence

section

variable {A : OA → OA → Sort v_A} [Category A]
variable {B : OB → OB → Sort v_B} [Category B]
variable {C : OC → OC → Sort v_C} [Category C]

/-- Any category is equivalent to itself. -/
def id : A ≅ A where
  fwd := Functor.id
  bwd := Functor.id
  fwd_bwd_iso_id := NatIso.from_eq Functor.post_id
  bwd_fwd_iso_id := NatIso.from_eq Functor.post_id

def comp (h0 : A ≅ B) (h1 : B ≅ C) : A ≅ C where
  fwd := h0.fwd ⋙ h1.fwd
  bwd := h1.bwd ⋙ h0.bwd
  fwd_bwd_iso_id := by
    sorry
  bwd_fwd_iso_id := by
    sorry

end

end Equivalence

end Category
