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

section

variable (F : (A ⨂ B) ⥤ C)

/-- A bifunctor acts on a pair of identities by producing the identity. -/
@[simp]
def map_id : F.map ⟨𝓐.id, 𝓑.id⟩ = @𝓒.id (F.obj x) := by
  suffices ⟨𝓐.id, 𝓑.id⟩ = @𝓐x𝓑.id x by
    rw [this]
    exact F.map_id
  rw [𝓐x𝓑.bi_compat_id]

/-- A bifunctor acts on a pair of composed functions in the natural way. -/
@[simp]
def map_comp :
F.map ⟨f0, g0⟩ ≫ F.map ⟨f1, g1⟩ =
F.map ⟨f0 ≫ f1, g0 ≫ g1⟩ := by
    suffices 𝓐x𝓑.comp ⟨f0, g0⟩ ⟨f1, g1⟩ = ⟨f0 ≫ f1, g0 ≫ g1⟩ by
      rw [←this, ←F.map_comp]
    rw [𝓐x𝓑.bi_compat_comp]

@[simp]
def map_comp_right
  {a : OA}
  {x y z: OB}
  {g0 : B x y}
  {g1 : B y z} :
  F.map ⟨@𝓐.id a, g0 ≫ g1⟩ =
  F.map (⟨𝓐.id, g0⟩ : (A ⨂ B) ⟨a, x⟩ ⟨a, y⟩) ≫
  F.map (⟨𝓐.id, g1⟩ : (A ⨂ B) ⟨a, y⟩ ⟨a, z⟩) := by
  calc
    _ = F.map ⟨@𝓐.id a ≫ 𝓐.id, g0 ≫ g1⟩ := by rw [𝓐.post_id]
    _ = _ := by rw [BiFunctor.map_comp]

/-- We can "curry" bifunctors, "evaluating" one side first.

This is analogous to how `(A × B) → C` is the same as `A → B → C`.
-/
def curry : A ⥤ (Nat B C) where
  obj a := {
    obj b := F.obj ⟨a, b⟩
    map f := F.map ⟨𝓐.id, f⟩
    map_id := by
      intros
      simp only [map_id]
    map_comp := by
      intros x y f z g
      simp only [map_comp_right]
  }
  map {a0 a1} (f : A a0 a1) := {
    on b := F.map ⟨f, 𝓑.id⟩
    natural := by
      intro b0 b1 g
      simp only [
        BiFunctor.map_comp,
        𝓐.post_id,
        𝓐.pre_id,
        𝓑.post_id,
        𝓑.pre_id
      ]
  }
  map_id := by
    intros
    rw [Nat.eq_iff_on_eq]
    intro x
    simp only [BiFunctor.map_id, Category.Struct.id, Nat.id]
  map_comp := by
    intros
    rw [Nat.eq_iff_on_eq]
    intro b
    simp only [BiFunctor.map_comp, Category.Struct.comp, Nat.comp, 𝓑.post_id]

/-- Convert a curried bifunctor back to its original form. -/
def uncurry (F : A ⥤ (Nat B C)) : A ⨂ B ⥤ C where
  obj := fun x => (F.obj x.fst).obj x.snd
  map {x y} := fun ⟨f, g⟩ => (F.map f).on x.snd ≫ (F.obj y.fst).map g
  map_id := by
    intros
    simp only [
      BiCategory.bi_compat_id,
      Functor.map_id,
      Struct.id,
      Nat.id_on,
      Category.post_id
    ]
  map_comp := by
    intro x y f z g
    calc
      _ =
      (F.map f.fst).on x.snd ≫
      ((F.map g.fst).on x.snd ≫ (F.obj z.fst).map f.snd) ≫
      (F.obj z.fst).map g.snd := by
        simp only [
          BiCategory.bi_compat_comp,
          Functor.map_comp,
          Nat.comp_on,
          Category.comp_assoc
        ]
      _ =
      ((F.map f.fst).on x.snd ≫ (F.obj y.fst).map f.snd) ≫
      ((F.map g.fst).on y.snd ≫ (F.obj z.fst).map g.snd) := by
        rw [Nat.natural]
        simp only [Category.comp_assoc]

end

 section

/-- There's a natural bifunctor that "evaluates" a functor on an object.

Objectwise, this maps a functor and an object to the functor evaluated at that point.

Mapwise, this maps a natural transformation and a function to the naturality square formed
at that function, using that transformation.
-/
def eval : (Nat A B) ⨂ A ⥤ B where
  obj := fun ⟨F, a⟩ => F.obj a
  map := by
    intro ⟨F, x⟩ ⟨G, y⟩ ⟨φ, f⟩
    exact (φ.on x ≫ G.map f)
  map_id := by
    intros
    simp only [Functor.map_id, Category.Struct.id, Nat.id_on, 𝓑.post_id]
  map_comp := by
    intro ⟨_, x⟩ ⟨G, y⟩ ⟨β, f⟩ ⟨H, _⟩ ⟨γ, g⟩
    calc
      _ = β.on x ≫ (γ.on x ≫ H.map f) ≫ H.map g := by
        simp only [Category.comp_assoc, Nat.comp_on, H.map_comp]
      _ = (β.on x ≫ G.map f) ≫ (γ.on y ≫ H.map g) := by
        simp only [γ.natural, Category.comp_assoc]
end

end BiFunctor

end Category
