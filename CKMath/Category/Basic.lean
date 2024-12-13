class CategoryStruct (O : Type u) where
  Hom : O → O → Type v
  id : (A : O) → Hom A A
  comp : Hom A B → Hom B C → Hom A C
