import PfaffianDescent.IndependentPerfectQuarticFieldPointSection
import PfaffianDescent.PerfectFieldClosedPointGeometricPosition
import AllCharacteristics.ClosedPointAlgebra

/- SOURCE ONLY / UNVERIFIED. Literal ground noncoplanar original closed
quartic point -> rational section of SAME original smooth cubic. No geometric
position, field/basis/affine differential/section certificate is input. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem independent_perfectField_noncoplanarClosedQuarticPoint_rational_section
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (h4 : (hypersurfaceToBase p hp).residueDegree x.1 = 4)
    (hplane : ¬ ∃ c : Fin 4 → K, c ≠ 0 ∧
      Ideal.Quotient.mk (equationIdeal p hp).toIdeal (homogeneousLinearForm c) ∈
        x.1.asHomogeneousIdeal.toIdeal) :
    ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) x.1
  letI := AllCharacteristics.closedPoint_moduleFinite (hypersurfaceToBase p hp) x
  let L := (hypersurface p hp).residueField x.1
  have hd : finrank K L = 4 :=
    (AllCharacteristics.closedPoint_finrank_eq_residueDegree
      (hypersurfaceToBase p hp) x).trans h4
  have hspan : ProjectiveGeometricGeneralPosition (equationIdeal p hp)
      ((hypersurface p hp).fromSpecResidueField x.1) :=
    perfectField_cubic_closedPoint_degree_four_general_position p hp x h4 hplane
  exact independent_perfectField_actualQuarticPoint_rational_section
    (K := K) (L := L) p hp hp0 ((hypersurface p hp).fromSpecResidueField x.1)
    (AllCharacteristics.pointAlgebra_spec (hypersurfaceToBase p hp) x.1).symm hd hspan

end PfaffianDescent
