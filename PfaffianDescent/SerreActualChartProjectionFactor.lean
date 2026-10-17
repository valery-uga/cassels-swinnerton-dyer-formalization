import Mathlib.CategoryTheory.Category.Basic

namespace PfaffianDescent
open CategoryTheory
universe u v

/-- Compose an actual chart factorization with a checked ambient projection
identity, before specializing to dependent scheme-module families. -/
theorem serreActualChartProjectionFactor
    {D : Type u} [Category.{v} D] {T A B C P Q : D}
    (f : T ⟶ A) (c : A ⟶ B) (t : T ⟶ C) (m : C ⟶ B)
    (π : B ⟶ P) (s : C ⟶ Q) (q : Q ⟶ P)
    (hf : f ≫ c = t ≫ m) (hm : m ≫ π = s ≫ q) :
    f ≫ c ≫ π = (t ≫ s) ≫ q := by
  rw [← Category.assoc, hf, Category.assoc, hm, ← Category.assoc]

end PfaffianDescent
