class Category.Struct {O : Sort u} (Mor : O → O → Sort v) where
  id : Mor X X
  comp : Mor A B → Mor B C → Mor A C

infixr:80 " ≫ " => Category.Struct.comp

class Category {O : Sort u} (Mor : O → O → Sort v) extends @Category.Struct O Mor where
  pre_id (f : Mor A B) : id ≫ f = f
  post_id (f : Mor A B) : f ≫ id = f
  comp_assoc (f : Mor A B) (g : Mor B C) (h : Mor C D) : (f ≫ g) ≫ h = f ≫ (g ≫ h)

def Fun (A B : Sort u) := A → B

instance Fun.category : Category Fun where
  id := id
  comp f g := g ∘ f
  pre_id := by intros ; rfl
  post_id := by intros ; rfl
  comp_assoc := by intros ; rfl
