import CKMath.Category.Definition
import CKMath.Category.Elementary
import CKMath.Category.Functor

namespace Category

variable [𝓐 : Category (O := OA) A]

/-- Represents the natural hom functor, mapping morphisms to functions between hom-sets. -/
def Hom (x : OA) : A ⥤ Fun where
  obj y := A x y
  map {a b} (f : A a b) := fun (g : A x a) ↦ g ≫ f
  map_id := by
    intros
    simp only [𝓐.post_id]
    rfl
  map_comp := by
    intros a b f c g
    funext φ
    calc
      _ = (φ ≫ f) ≫ g := by rw [comp_assoc]
      _ = _ := by trivial


end Category
