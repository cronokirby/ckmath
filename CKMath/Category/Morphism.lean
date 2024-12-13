import CKMath.Category.Definition

namespace Category

variable [𝓒 : Category O]

/-- An isomorphism demonstrates that two objects cannot be distinguished in this category.

From a category-theoretic point of view, it's really uncouth to say anything more than that
two objects are isomorphic. Lean equality depends on the particular encoding of the category,
and not on the essence of the object we're studying.
-/
structure Isomorphism (A B) where
  f : 𝓒.Mor A B
  f_inv : 𝓒.Mor B A
  pre_inv : f_inv ≫ f = 𝓒.id
  post_inv : f ≫ f_inv = 𝓒.id

infix:100 " ≅ " => Isomorphism

namespace Isomorphism

/-- An isomorphism can be flipped, and considered in the other direction. -/
def flip {A B : O} (i : A ≅ B) : B ≅ A :=
  ⟨i.f_inv, i.f, i.post_inv, i.pre_inv⟩

/-- Flipping an isomorphism twice produces the original isomorphism. -/
@[simp]
def flip_flip_eq {A B : O} (i : A ≅ B) : i.flip.flip = i := rfl

/-- Isomorphisms can be composed together. -/
def trans {A B C : O} (i0 : A ≅ B) (i1 : B ≅ C) : A ≅ C := {
  f := i0.f ≫ i1.f,
  f_inv := i1.f_inv ≫ i0.f_inv,
  post_inv := by
    calc
      _ = i0.f ≫ (i1.f ≫ i1.f_inv) ≫ i0.f_inv := by simp only [𝓒.comp_assoc]
      _ = _ := by simp only [i0.post_inv, i1.post_inv, 𝓒.pre_id]
  pre_inv := by
      calc
      _ = i1.f_inv ≫ (i0.f_inv ≫ i0.f) ≫ i1.f := by simp only [𝓒.comp_assoc]
      _ = _ := by simp only [i0.pre_inv, i1.pre_inv, 𝓒.pre_id]
}

end Isomorphism

end Category
