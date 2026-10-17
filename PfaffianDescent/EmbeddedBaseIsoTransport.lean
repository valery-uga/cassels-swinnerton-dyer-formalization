import Mathlib.AlgebraicGeometry.Morphisms.Basic

/-! Transport scheme-theoretic equality with a base locus through the exact
source, base-scheme and ambient coordinate comparison squares. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory
universe u

/-- This auxiliary transport keeps the given ambient map, including its
nonreduced source. The comparison squares are proved by the geometric caller. -/
theorem exists_embeddedBaseIso_of_comparison_squares
    {Z Y B C P Q : Scheme.{u}}
    (z : Z ≅ Y) (b : B ≅ C) (a : P ≅ Q)
    (i : B ⟶ P) (j : C ⟶ Q) (q : Z ⟶ P) (r : Y ⟶ Q)
    (hb : b.hom ≫ j = i ≫ a.hom)
    (hq : q ≫ a.hom = z.hom ≫ r)
    (hl : ∃ l : Y ⟶ C, IsIso l ∧ l ≫ j = r) :
    ∃ l : Z ⟶ B, IsIso l ∧ l ≫ i = q := by
  obtain ⟨l, hlIso, hl⟩ := hl
  letI : IsIso l := hlIso
  have hbj : b.inv ≫ i ≫ a.hom = j := by
    rw [← hb, ← Category.assoc, b.inv_hom_id, Category.id_comp]
  refine ⟨z.hom ≫ l ≫ b.inv, inferInstance, ?_⟩
  apply (cancel_mono a.hom).mp
  calc
    (z.hom ≫ l ≫ b.inv) ≫ i ≫ a.hom =
        z.hom ≫ l ≫ (b.inv ≫ i ≫ a.hom) := by simp only [Category.assoc]
    _ = z.hom ≫ l ≫ j := by rw [hbj]
    _ = z.hom ≫ r := by rw [hl]
    _ = q ≫ a.hom := hq.symm

end PfaffianDescent
