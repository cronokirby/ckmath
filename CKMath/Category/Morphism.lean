import CKMath.Category.Definition

structure OfIso (α) where
  unOfIso : α

namespace Category

variable [𝓒 : Category O]

/-- An isomorphism demonstrates that two objects cannot be distinguished in this category.

From a category-theoretic point of view, it's really uncouth to say anything more than that
two objects are isomorphic. Lean equality depends on the particular encoding of the category,
and not on the essence of the object we're studying.
-/
@[ext]
structure Isomorphism (A B) where
  f : 𝓒.Mor A B
  f_inv : 𝓒.Mor B A
  pre_inv : f_inv ≫ f = 𝓒.id
  post_inv : f ≫ f_inv = 𝓒.id

infix:100 " ≅ " => Isomorphism

namespace Isomorphism

def id {A : O}: A ≅ A := {
  f := 𝓒.id,
  f_inv := 𝓒.id,
  pre_inv := by
    simp only [𝓒.post_id]
  post_inv := by
    simp only [𝓒.post_id]
}

/-- An isomorphism can be flipped, and considered in the other direction. -/
def flip {A B : O} (i : A ≅ B) : B ≅ A :=
  ⟨i.f_inv, i.f, i.post_inv, i.pre_inv⟩

/-- Flipping an isomorphism twice produces the original isomorphism. -/
@[simp]
def flip_flip_eq {A B : O} (i : A ≅ B) : i.flip.flip = i := rfl

/-- Isomorphisms can be composed together. -/
def comp {A B C : O} (i0 : A ≅ B) (i1 : B ≅ C) : A ≅ C := {
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

theorem comp_lemma
  {A B C : O}
  (F : A ≅ B)
  (G : B ≅ C)
  (H : A ≅ C)
  (h1 : F.f ≫ G.f = H.f)
  (h2 : G.f_inv ≫ F.f_inv = H.f_inv) :
  F.comp G = H := by
    ext
    . exact h1
    . exact h2

end Isomorphism

def Iso : (Category (OfIso O)) where
  Mor (A B) := A.unOfIso ≅ B.unOfIso
  id := Isomorphism.id
  comp := Isomorphism.comp
  pre_id := by
    intro _ _ f
    apply Isomorphism.comp_lemma
    . change 𝓒.comp 𝓒.id f.f = f.f
      exact 𝓒.pre_id f.f
    . change 𝓒.comp f.f_inv 𝓒.id = f.f_inv
      exact 𝓒.post_id f.f_inv
  post_id := by
    intro _ _ f
    apply Isomorphism.comp_lemma
    . change 𝓒.comp f.f 𝓒.id = f.f
      exact 𝓒.post_id f.f
    . change 𝓒.comp 𝓒.id f.f_inv = f.f_inv
      exact 𝓒.pre_id f.f_inv
  comp_assoc := by
    intro _ _ _ _ f g h
    change Isomorphism.comp f (Isomorphism.comp g h) =
           Isomorphism.comp (Isomorphism.comp f g) h
    ext
    . change f.f ≫ (g.f ≫ h.f) = (f.f ≫ g.f) ≫ h.f
      simp only [𝓒.comp_assoc]
    . change (h.f_inv ≫ g.f_inv) ≫ f.f_inv = h.f_inv ≫ (g.f_inv ≫ f.f_inv)
      simp only [𝓒.comp_assoc]

end Category
