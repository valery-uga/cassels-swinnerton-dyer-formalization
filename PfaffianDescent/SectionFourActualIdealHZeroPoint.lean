import PfaffianDescent.ActualP3IdealQuadraticGlobalBase
import PfaffianDescent.IntrinsicFullQuadraticBasePoint

/-! UNVERIFIED: the finite full base of the actual H0(I_Z(2)) gives a
section on the SAME original cubic over any field, retaining nilpotents. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem sectionFour_section_of_cubic_of_finite_actual_ideal_quadratic_global_base
    {K : Type u} [Field K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    {Z : Scheme.{u}} (j : Z ⟶ hypersurface F hF) [IsClosedImmersion j]
    [IsFinite (j ≫ hypersurfaceToBase F hF)]
    (hZ : AllCharacteristics.finiteSchemeRank (j ≫ hypersurfaceToBase F hF) = 8)
    [IsFinite (toBase
      (p3ActualIdealQuadraticGlobalBaseIdeal (j ≫ hypersurfaceToAmbient F hF)))] :
    ∃ s : Spec (.of K) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _ := by
  letI : IsFinite (toBase
      (intrinsicFullQuadraticBaseIdeal (j ≫ hypersurfaceToAmbient F hF))) := by
    rw [← p3ActualIdealQuadraticGlobalBaseIdeal_eq_intrinsic]
    infer_instance
  exact sectionFour_section_of_cubic_of_finite_intrinsic_full_quadratic_base F hF j hZ

end PfaffianDescent
