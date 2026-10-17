import PfaffianDescent.VoisinSelectedLocalizationFractionField

/-! Generic values of pulled-back sections on a selected ordered chart. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory

universe u

/-- Evaluation of a section pulled back to the selected ordered chart
agrees with evaluation at the chart's generic point after passage through
the determinant-open fraction field and the ordered residue field. -/
theorem affineOpenImmersion_localizedFraction_generic_appTop_value
    {U O V : Scheme.{u}} [IsAffine U] [IsIntegral U] [IsIntegral O]
    (i : U ⟶ O) [IsOpenImmersion i]
    (s : Γ(U, ⊤)) (hs : s ≠ 0)
    (t : U ⟶ V) (a : Γ(V, ⊤)) :
    (i.residueFieldMap (genericPoint U)).hom
      (affineOpenImmersion_localizedFractionEquivGenericImageResidueField i s hs
        (algebraMap (Localization.Away s)
          (FractionRing (Localization.Away s))
          (algebraMap Γ(U, ⊤) (Localization.Away s)
            (t.appTop.hom a)))) =
      (t.residueFieldMap (genericPoint U)).hom
        (V.Γevaluation (t (genericPoint U)) a) := by
  rw [affineOpenImmersion_localizedFractionEquivGenericImageResidueField_algebraMap]
  exact (Scheme.Γevaluation_naturality_apply t (genericPoint U) a).symm

end PfaffianDescent
