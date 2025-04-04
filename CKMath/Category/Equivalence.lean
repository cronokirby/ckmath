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

infixr:82 " ≈ " => Equivalence


namespace Equivalence

section

variable {A : OA → OA → Sort v_A} [Category A]
variable {B : OB → OB → Sort v_B} [Category B]
variable {C : OC → OC → Sort v_C} [Category C]

/-- Any category is equivalent to itself. -/
def id : A ≈ A where
  fwd := Functor.id
  bwd := Functor.id
  fwd_bwd_iso_id := NatIso.from_eq Functor.post_id
  bwd_fwd_iso_id := NatIso.from_eq Functor.post_id

/-- Equivalences between categories compose. -/
def comp (h0 : A ≈ B) (h1 : B ≈ C) : A ≈ C := {
  fwd := h0.fwd ⋙ h1.fwd,
  bwd := h1.bwd ⋙ h0.bwd,
  fwd_bwd_iso_id := by
    calc
    _ ≅ h0.fwd ⋙ (h1.fwd ⋙ h1.bwd) ⋙ h0.bwd := NatIso.from_eq rfl
    _ ≅ h0.fwd ⋙ Functor.id ⋙ h0.bwd := by
      apply NatIso.hcomp
      . exact NatIso.from_eq rfl
      . apply NatIso.hcomp
        . exact h1.fwd_bwd_iso_id
        . exact NatIso.from_eq rfl
    _ ≅ h0.fwd ⋙ h0.bwd := NatIso.from_eq rfl
    _ ≅ Functor.id := h0.fwd_bwd_iso_id
  bwd_fwd_iso_id := by
    calc
    _ ≅ h1.bwd ⋙ (h0.bwd ⋙ h0.fwd) ⋙ h1.fwd := NatIso.from_eq rfl
    _ ≅ h1.bwd ⋙ Functor.id ⋙ h1.fwd := by
      apply NatIso.hcomp
      . exact NatIso.from_eq rfl
      . apply NatIso.hcomp
        . exact h0.bwd_fwd_iso_id
        . exact NatIso.from_eq rfl
    _ ≅ h1.bwd ⋙ h1.fwd := NatIso.from_eq rfl
    _ ≅ Functor.id := h1.bwd_fwd_iso_id
}

/-- An equivalence between categories yields an equivalence in the other direction. -/
def symm (h : A ≈ B) : B ≈ A where
  fwd := h.bwd
  bwd := h.fwd
  fwd_bwd_iso_id := h.bwd_fwd_iso_id
  bwd_fwd_iso_id := h.fwd_bwd_iso_id

@[simp]
def symm_symm_eq (h : A ≈ B) : h.symm.symm = h := by rfl

/-- Apply an equivalence to the input of a functor category. -/
def transport_left (h : A ≈ B) : Nat A C ≈ Nat B C where
  fwd := whisker_post h.bwd
  bwd := whisker_post h.fwd
  fwd_bwd_iso_id := sorry
  bwd_fwd_iso_id := sorry

/-- Apply an equivalence to the output of a functor category. -/
def transport_right (h : A ≈ B) : Nat C A ≈ Nat C B where
  fwd := whisker_pre h.fwd
  bwd := whisker_pre h.bwd
  fwd_bwd_iso_id := sorry
  bwd_fwd_iso_id := sorry

end

end Equivalence

end Category
