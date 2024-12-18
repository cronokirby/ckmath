import CKMath.Category.Definition
import CKMath.Category.Elementary

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

/-- Notation to be able to write `A ≅ B` instead of `Isomorphism A B`-/
infix:100 " ≅ " => Isomorphism

namespace Isomorphism

/-- If two isomorphisms have the same main function, their inverses must also match.

This is a useful technical lemma, since we can then use it to prove identities about isomorphisms
without having to prove the same result for both the carrier and the inverse.
-/
theorem out_eq_then_inv_eq {A B : O} {f g : A ≅ B} : f.out = g.out → f.inv = g.inv := by
  intro out_eq
  have h0 : g.inv ≫ f.out = g.inv ≫ g.out := by
    congr
  rw [g.pre_inv] at h0
  have h1 : (g.inv ≫ f.out) ≫ f.inv = 𝓒.id ≫ f.inv := by
    congr
  rw [←𝓒.comp_assoc, f.post_inv, 𝓒.post_id, 𝓒.pre_id] at h1
  exact Eq.symm h1

/-- To prove that two isomorphisms are equal, it suffices to show their carriers are equal.

This is a key simplifier for equalities of isomorphisims.
-/
@[simp]
theorem eq_iff_out_eq {A B : O} {f g : A ≅ B} : f = g ↔ f.out = g.out := by
  apply Iff.intro
  . intro h
    rw [h]
  . intro h
    suffices f.inv = g.inv by
      ext
      exact h
      exact this
    exact out_eq_then_inv_eq h

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

/-- When showing that the composition of isomorphisms -/
@[simp]
theorem comp_out_eq_comp
  {A B C : O}
  {F : A ≅ B}
  {G : B ≅ C}
  : (F.comp G).out = F.out ≫ G.out := by rfl

/-- Any object is isomorphic to itself, as demonstrated by the identity function. -/
def id {A : O}: A ≅ A := {
  out := 𝓒.id,
  inv := 𝓒.id,
  pre_inv := by
    simp only [𝓒.post_id]
  post_inv := by
    simp only [𝓒.post_id]
}

/-- Simplifying the identity isomorphism to the identity morphism.

This is useful because proving identities about isomorphisms boils down
to proving identities about the carrier functions.
-/
@[simp]
theorem id_out_eq_id {A : O} : (@id _ _ A).out = 𝓒.id := by rfl

end Isomorphism
end Category

/-- A wrapper structure to define the category of isomorphisms. -/
structure OfIso (α) where
  unOfIso : α

namespace Category

variable [𝓒 : Category O]

/-- Isomorphisms form a category. -/
def Iso : (Category (OfIso O)) where
  Mor (A B) := A.unOfIso ≅ B.unOfIso
  id := Isomorphism.id
  comp := Isomorphism.comp
  pre_id := by
    intros
    simp only [
      Isomorphism.comp_out_eq_comp,
      Isomorphism.eq_iff_out_eq,
      Isomorphism.id_out_eq_id,
      pre_id_simp
    ]
  post_id := by
    intros
    simp only [
      Isomorphism.eq_iff_out_eq,
      Isomorphism.comp_out_eq_comp,
      Isomorphism.id_out_eq_id,
      post_id_simp
    ]
  comp_assoc := by
    intros
    simp only [Isomorphism.eq_iff_out_eq, Isomorphism.comp_out_eq_comp, comp_assoc_simp]

end Category

namespace Category

variable [𝓒 : Category O]

/-- The property of being a monomorphism, i.e. preserving equalities by post-composition. -/
def is_mono {B C : O} (f : 𝓒.Mor B C) : Prop :=
  ∀ {A : O} {g h : 𝓒.Mor A B}, g ≫ f = h ≫ f → g = h

/-- The property of being an epimorphism, i.e. being a monomorphism in the opposite category. -/
def is_epi {A B : O} (f : 𝓒.Mor A B) : Prop :=
  @is_mono (Opposite O) 𝓒.Op (Opposite.mk B) (Opposite.mk A) f

/-- The claass of functions that are monomorphisms -/
class Mono (f : 𝓒.Mor A B) where
  w_mono : 𝓒.is_mono f

class Epi (f : 𝓒.Mor A B) where
  w_epi : 𝓒.is_epi f

end Category
