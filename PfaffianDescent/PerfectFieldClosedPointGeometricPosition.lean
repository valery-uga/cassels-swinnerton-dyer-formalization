import PfaffianDescent.PerfectFieldPointGeometricPosition
import AllCharacteristics.ClosedPointAlgebra
import AllCharacteristics.HomogeneousProjectiveAmbient

/-! The noncoplanar part of the paper's position lemma, for literal closed
points of residue degree four and five over the standing perfect base field.
General position refers to actual algebraic-closure-valued scheme points of
the original residue-field immersion. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem perfectField_cubic_closedPoint_degree_four_or_five_general_position
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 4 ∨
      (hypersurfaceToBase p hp).residueDegree x.1 = 5)
    (hplane : ¬ ∃ c : Fin 4 → K, c ≠ 0 ∧
      Ideal.Quotient.mk (equationIdeal p hp).toIdeal (homogeneousLinearForm c) ∈
        x.1.asHomogeneousIdeal.toIdeal) :
    ProjectiveGeometricGeneralPosition (equationIdeal p hp)
      ((hypersurface p hp).fromSpecResidueField x.1) := by
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) x.1
  letI := AllCharacteristics.closedPoint_moduleFinite (hypersurfaceToBase p hp) x
  have hdim : Module.finrank K ((hypersurface p hp).residueField x.1) = 4 ∨
      Module.finrank K ((hypersurface p hp).residueField x.1) = 5 := by
    rw [AllCharacteristics.closedPoint_finrank_eq_residueDegree
      (hypersurfaceToBase p hp) x]
    exact hx
  exact perfectField_fieldPoint_projectiveGeometricGeneralPosition
    (K := K) (L := (hypersurface p hp).residueField x.1)
    (equationIdeal p hp) ((hypersurface p hp).fromSpecResidueField x.1)
    (AllCharacteristics.pointAlgebra_spec (hypersurfaceToBase p hp) x.1).symm hdim
    (by
      rintro ⟨c, hc, hmem⟩
      apply hplane
      refine ⟨c, hc, ?_⟩
      have hpoint : ((hypersurface p hp).fromSpecResidueField x.1)
          (IsLocalRing.closedPoint ((hypersurface p hp).residueField x.1)) = x.1 :=
        (hypersurface p hp).fromSpecResidueField_apply x.1 _
      erw [hpoint] at hmem
      exact hmem)

theorem perfectField_cubic_closedPoint_degree_four_general_position
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 4)
    (hplane : ¬ ∃ c : Fin 4 → K, c ≠ 0 ∧
      Ideal.Quotient.mk (equationIdeal p hp).toIdeal (homogeneousLinearForm c) ∈
        x.1.asHomogeneousIdeal.toIdeal) :
    ProjectiveGeometricGeneralPosition (equationIdeal p hp)
      ((hypersurface p hp).fromSpecResidueField x.1) :=
  perfectField_cubic_closedPoint_degree_four_or_five_general_position
    p hp x (Or.inl hx) hplane

theorem perfectField_cubic_closedPoint_degree_five_general_position
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 5)
    (hplane : ¬ ∃ c : Fin 4 → K, c ≠ 0 ∧
      Ideal.Quotient.mk (equationIdeal p hp).toIdeal (homogeneousLinearForm c) ∈
        x.1.asHomogeneousIdeal.toIdeal) :
    ProjectiveGeometricGeneralPosition (equationIdeal p hp)
      ((hypersurface p hp).fromSpecResidueField x.1) :=
  perfectField_cubic_closedPoint_degree_four_or_five_general_position
    p hp x (Or.inr hx) hplane

end PfaffianDescent
