import CKMath.Category.Definition

namespace Category

variable (O : Type u) [𝓒 : Category O]

@[simp]
def whisker_pre (f g : 𝓒.Mor A B) (h : 𝓒.Mor B C) (_ : f = g) : f ≫ h = g ≫ h := by
  congr

@[simp]
def whisker_post (f g : 𝓒.Mor B C) (h : 𝓒.Mor A B) (_ : f = g) : h ≫ f = h ≫ g := by
  congr

/-- A non-trivial technical result involving the gluing of two commutative diagrams. -/
theorem double_square_commutes
  {a0 : 𝓒.Mor A0 A1}
  {a1 : 𝓒.Mor A1 A2}
  {c0 : 𝓒.Mor B0 B1}
  {c1 : 𝓒.Mor B1 B2}
  {b0 : 𝓒.Mor A0 B0}
  {b1 : 𝓒.Mor A1 B1}
  {b2 : 𝓒.Mor A2 B2}
  (square0 : a0 ≫ b1 = b0 ≫ c0)
  (square1: a1 ≫ b2 = b1 ≫ c1) :
  (a0 ≫ a1 ≫ b2 = b0 ≫ c0 ≫ c1) := by
  simp [square0, square1, 𝓒.comp_assoc]

end Category
