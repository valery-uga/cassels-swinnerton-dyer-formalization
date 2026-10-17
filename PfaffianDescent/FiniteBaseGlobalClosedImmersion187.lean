import Mathlib.AlgebraicGeometry.Morphisms.Finite

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

/-- Native finite-over-base plus separated ambient base globalizes the
SAME closed-in-open composite, with its original maps used verbatim. -/
lemma globalClosedImmersion_of_finite_base187
    {B U X Z : Scheme.{u}} (F : X ⟶ B) [IsSeparated F]
    (j : Z ⟶ U) [IsClosedImmersion j]
    (a : U ⟶ X) [IsOpenImmersion a]
    (p : Z ⟶ B) [IsFinite p] (hbase : (j ≫ a) ≫ F = p) :
    IsClosedImmersion (j ≫ a) := by
  letI : IsFinite ((j ≫ a) ≫ F) := hbase.symm ▸ (inferInstance : IsFinite p)
  letI : IsFinite (j ≫ a) := IsFinite.of_comp (j ≫ a) F
  exact (IsClosedImmersion.iff_isFinite_and_mono (j ≫ a)).mpr
    ⟨inferInstance, inferInstance⟩

end PfaffianDescent
