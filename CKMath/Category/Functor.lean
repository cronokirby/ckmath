import CKMath.Category.Definition
import CKMath.Category.Morphism

namespace Category

/-- A pseudo functor is a map between categories, which may be structure preserving.

This class exists to let us easily define functors incrementally, by giving their definition
before we're ready to prove properties.
-/
structure PseudoFunctor (C) [𝓒 : Category.Struct C] (D) [𝓓 : Category.Struct D] where
  obj : C → O
  map {A B : C} : 𝓒.Mor A B → 𝓓.Mor (obj A) (obj B)

/-- A functor is a structure preserving map between categories. -/
structure Functor (C) [𝓒 : Category C] (D) [𝓓 : Category D] extends PseudoFunctor C D where
  map_id {X : C} : @map X X 𝓒.id = 𝓓.id
  map_comp {X Y Z : C} {f : 𝓒.Mor X Y} {g : 𝓒.Mor Y Z}: map (f ≫ g) = map f ≫ map g

namespace Functor

variable [𝓒 : Category C] [𝓓 : Category D] [𝓔 : Category E]

def comp (F : Functor C D) (G : Functor D E) : Functor C E := {
  obj := G.obj ∘ F.obj,
  map := G.map ∘ F.map,
  map_id := by
    intros
    simp only [Function.comp_apply, F.map_id, G.map_id]
  map_comp := by
    intros
    simp only [Function.comp_apply]
    rw [F.map_comp, G.map_comp]
}

/-- Technical simplifier to work with composed functors. -/
@[simp]
theorem comp_map
  {F : Functor C D}
  {G : Functor D E}
  {f : 𝓒.Mor A B} :
  (F.comp G).map f = G.map (F.map f) := by
  trivial

/-- A functor preserves (among many such diagrams) a commutative square.

This is a useful intermediate lemma
-/
theorem map_square
  {F : Functor C D}
  {f_00_01 : 𝓒.Mor A00 A01}
  {f_00_10 : 𝓒.Mor A00 A10}
  {f_01_11 : 𝓒.Mor A01 A11}
  {f_10_11 : 𝓒.Mor A10 A11} :
  (f_00_01 ≫ f_01_11 = f_00_10 ≫ f_10_11) →
  ((F.map f_00_01) ≫ (F.map f_01_11) = (F.map f_00_10) ≫ (F.map f_10_11)) := by
    intro h
    rw [←F.map_comp, ←F.map_comp, h]

/-- Functors map isomorphisms to isomorphisms. -/
def map_iso (F : Functor C D) (i : A ≅ B) : 𝓓.Isomorphism (F.obj A) (F.obj B) := {
  out := F.map i.out,
  inv := F.map i.inv,
  pre_inv := by
    rw [←F.map_comp, i.pre_inv]
    exact F.map_id
  post_inv := by
    rw [←F.map_comp, i.post_inv]
    exact F.map_id
}

@[ext]
structure PreMorphism (F G : Functor C D) where
  on (c : C) : 𝓓.Mor (F.obj c) (G.obj c)

/-- Un morphisme de foncteurs. -/
@[ext]
structure Morphism (F G) extends @PreMorphism C D _ _ F G where
  natural : ∀ f : 𝓒.Mor a b, on a ≫ G.map f = F.map f ≫ on b

infixr:80 " ⇒ " => Morphism

def id_morphism (F : Functor C D) : F ⇒ F where
  on _ := 𝓓.id
  natural := by
    simp only [pre_id_simp, post_id_simp, implies_true]

namespace Morphism

section

private def id {F : Functor C D} : F ⇒ F := F.id_morphism

@[simp]
private theorem id_on {F : Functor C D} {c : C} : (@id _ _ _ _ F).on c = 𝓓.id := by trivial

private def comp {F G H : Functor C D} (α : F ⇒ G) (β : G ⇒ H) : F ⇒ H := {
  on c := α.on c ≫ β.on c,
  natural := by
    intro a b f
    suffices (α.on a ≫ β.on a) ≫ H.map f = F.map f ≫ (α.on b ≫ β.on b) by
      trivial
    rw [comp_assoc]
    simp only [β.natural, ←comp_assoc, α.natural]
}

@[simp]
theorem comp_on {F G H : Functor C D} {α : F ⇒ G} {β : G ⇒ H} {c : C} : (α.comp β).on c = α.on c ≫ β.on c := by trivial

private theorem pre_id {F G : Functor C D} (α : F ⇒ G) : id.comp α = α := by
  ext
  simp only [comp_on, id_on, 𝓓.pre_id]

private theorem post_id {F G : Functor C D} (α : F ⇒ G) : α.comp id = α := by
  ext
  simp only [comp_on, id_on, 𝓓.post_id]

private theorem comp_assoc
  {F G H E : Functor C D}
  (α : F ⇒ G)
  (β : G ⇒ H)
  (γ : H ⇒ E) :
  (α.comp β).comp γ = α.comp (β.comp γ) := by
  ext
  simp only [comp_on, 𝓓.comp_assoc]

instance instCategoryStruct : Category.Struct (Functor C D) :=
  ⟨Morphism, id, comp⟩

/-- Functors between two categories form a category, whose morphisms are given by natural transformations. -/
instance instCategory : Category (Functor C D) :=
  ⟨pre_id, post_id, comp_assoc⟩

end

/-- Whisker a natural transformation before a functor.

Another way of looking at this is horizontal composition with the identity transformation on the right.
-/
def whisker_pre {F G : Functor C D} (α : F ⇒ G) (H : Functor D E) : F.comp H ⇒ G.comp H where
  on c := H.map (α.on c)
  natural := by
    intros
    apply H.map_square
    apply α.natural

/-- c.f. `whisker_pre` -/
def whisker_post {F G : Functor D E} (α : F ⇒ G) (H : Functor C D) : H.comp F ⇒ H.comp G where
  on c := α.on (H.obj c)
  natural := by
    intros
    simp only [comp_map, α.natural]

@[simp]
theorem whisker_pre_id {F : Functor C D} {H : Functor D E} : F.id_morphism.whisker_pre H = (F.comp H).id_morphism := by
  simp only [whisker_pre, id_morphism, H.map_id]

@[simp]
theorem whisker_post_id {F : Functor C D} {H : Functor D E} : H.id_morphism.whisker_post F = (F.comp H).id_morphism := by
  simp only [whisker_post, id_morphism]

end Morphism

end Functor

end Category
