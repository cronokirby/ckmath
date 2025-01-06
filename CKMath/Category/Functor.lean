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

namespace Morphism

section category

def id {F : Functor C D} : F ⇒ F := {
  on _ := 𝓓.id,
  natural := by
    simp only [pre_id_simp, post_id_simp, implies_true]
}

@[simp]
def id_on {F : Functor C D} {c : C} : (@id _ _ _ _ F).on c = 𝓓.id := by trivial

def comp {F G H : Functor C D} (α : F ⇒ G) (β : G ⇒ H) : F ⇒ H := {
  on c := α.on c ≫ β.on c,
  natural := by
    intro a b f
    suffices (α.on a ≫ β.on a) ≫ H.map f = F.map f ≫ (α.on b ≫ β.on b) by
      trivial
    rw [comp_assoc]
    simp only [β.natural, ←comp_assoc, α.natural]
}

@[simp]
def comp_on {F G H : Functor C D} {α : F ⇒ G} {β : G ⇒ H} {c : C} : (α.comp β).on c = α.on c ≫ β.on c := by trivial

def pre_id {F G : Functor C D} (α : F ⇒ G) : id.comp α = α := by
  ext
  simp only [comp_on, id_on, 𝓓.pre_id]

def post_id {F G : Functor C D} (α : F ⇒ G) : α.comp id = α := by
  ext
  simp only [comp_on, id_on, 𝓓.post_id]

def comp_assoc
  {F G H E : Functor C D}
  (α : F ⇒ G)
  (β : G ⇒ H)
  (γ : H ⇒ E) :
  (α.comp β).comp γ = α.comp (β.comp γ) := by
  ext
  simp only [comp_on, 𝓓.comp_assoc]

instance instCategoryStruct : Category.Struct (Functor C D) :=
  ⟨Morphism, id, comp⟩

def instCategory : Category (Functor C D) :=
  ⟨pre_id, post_id, comp_assoc⟩

end category

end Morphism

end Functor

end Category
