import CKMath.Category.Definition
import CKMath.Category.Elementary
import CKMath.Category.Functor

namespace Category

variable [𝓐 : Category (O := OA) A]

/-- Represents the hom functor as an explicit bifunctor. -/
def Hom : (Op A) ⨂ A ⥤ Fun where
  obj := fun ⟨x, y⟩ ↦ A x y
  map := fun ⟨f, g⟩ ↦ fun φ ↦ f.unop ≫ φ ≫ g
  map_id := by
    intros
    simp only [Op.unop_id_eq_id, Category.pre_id, Category.post_id]
    rfl
  map_comp := by
    intro x y f z g
    funext ψ
    rw [Fun.comp_apply]
    simp only [Op.unop_comp_eq_comp_unop, Category.comp_assoc]


end Category
