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
  out : 𝓒.Mor A B
  inv : 𝓒.Mor B A
  pre_inv : inv ≫ out = 𝓒.id
  post_inv : out ≫ inv = 𝓒.id

infix:100 " ≅ " => Isomorphism

namespace Isomorphism

def out_eq_then_inv_eq {A B : O} {f g : A ≅ B} : f.out = g.out → f.inv = g.inv := by
  intro out_eq
  have h0 : g.inv ≫ f.out = g.inv ≫ g.out := by
    congr
  rw [g.pre_inv] at h0
  have h1 : (g.inv ≫ f.out) ≫ f.inv = 𝓒.id ≫ f.inv := by
    congr
  rw [←𝓒.comp_assoc, f.post_inv, 𝓒.post_id, 𝓒.pre_id] at h1
  exact Eq.symm h1

@[simp]
def eq_iff_out_eq {A B : O} {f g : A ≅ B} : f = g ↔ f.out = g.out := by
  apply Iff.intro
  . intro h
    rw [h]
  . intro h
    suffices f.inv = g.inv by
      ext
      exact h
      exact this
    exact out_eq_then_inv_eq h

def id {A : O}: A ≅ A := {
  out := 𝓒.id,
  inv := 𝓒.id,
  pre_inv := by
    simp only [𝓒.post_id]
  post_inv := by
    simp only [𝓒.post_id]
}

/-- An isomorphism can be flipped, and considered in the other direction. -/
def flip {A B : O} (i : A ≅ B) : B ≅ A :=
  ⟨i.inv, i.out, i.post_inv, i.pre_inv⟩

/-- Flipping an isomorphism twice produces the original isomorphism. -/
@[simp]
def flip_flip_eq {A B : O} (i : A ≅ B) : i.flip.flip = i := rfl

/-- Isomorphisms can be composed together. -/
def comp {A B C : O} (i0 : A ≅ B) (i1 : B ≅ C) : A ≅ C := {
  out := i0.out ≫ i1.out,
  inv := i1.inv ≫ i0.inv,
  post_inv := by
    calc
      _ = i0.out ≫ (i1.out ≫ i1.inv) ≫ i0.inv := by simp only [𝓒.comp_assoc]
      _ = _ := by simp only [i0.post_inv, i1.post_inv, 𝓒.pre_id]
  pre_inv := by
      calc
      _ = i1.inv ≫ (i0.inv ≫ i0.out) ≫ i1.out := by simp only [𝓒.comp_assoc]
      _ = _ := by simp only [i0.pre_inv, i1.pre_inv, 𝓒.pre_id]
}

@[simp]
theorem comp_lemma
  {A B C : O}
  {F : A ≅ B}
  {G : B ≅ C}
  {H : A ≅ C}
  : F.comp G = H ↔ F.out ≫ G.out = H.out := eq_iff_out_eq

end Isomorphism

def Iso : (Category (OfIso O)) where
  Mor (A B) := A.unOfIso ≅ B.unOfIso
  id := Isomorphism.id
  comp := Isomorphism.comp
  pre_id := by
    intro _ _ f
    apply Isomorphism.comp_lemma.mpr
    change 𝓒.id ≫ f.out = f.out
    simp only [𝓒.pre_id]
  post_id := by
    intro _ _ f
    apply Isomorphism.comp_lemma.mpr
    change f.out ≫ 𝓒.id = f.out
    simp only [𝓒.post_id]
  comp_assoc := by
    intro _ _ _ _ f g h
    simp only [Isomorphism.comp_lemma]
    change f.out ≫ (g.out ≫ h.out) = (f.out ≫ g.out) ≫ h.out
    simp only [𝓒.comp_assoc]

end Category
