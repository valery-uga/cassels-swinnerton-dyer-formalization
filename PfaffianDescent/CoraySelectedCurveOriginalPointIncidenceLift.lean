import PfaffianDescent.CorayGenericNormalizationOriginalCubicProperMap
import PfaffianDescent.CoraySelectedCurveOriginalClosedPoint

/-! A natural ORIGINAL point incidence on the SAME actual selected curve
constructs its actual closed lift, own residue-map isomorphism and full K
degree. No closed lift, degree certificate or regularity is supplied.
The accepted exact-chart q-zero producer already derives this incidence.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace AllCharacteristics
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The OWN original point lies on the OWN selected q curve. Its closed
curve point and all required original residue-field/degree data are derived
from the actual canonical closed immersion. No integrality is needed. -/
theorem selectedCurve_originalClosedPoint_of_originalPoint_mem_image
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (n : ℕ) (hq : q.IsHomogeneous n)
    (P : closedPoints (hypersurface p hp))
    (hP : P.1 ∈ Set.range (cubicSecondEquationCurveImmersion p q hp n hq)) :
    ∃ Q : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)),
      cubicSecondEquationCurveImmersion p q hp n hq Q.1 = P.1 ∧
      IsIso ((cubicSecondEquationCurveImmersion p q hp n hq).residueFieldMap Q.1) ∧
      (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree Q.1 =
        (hypersurfaceToBase p hp).residueDegree P.1 := by
  classical
  let X := scheme (projectiveIntersectionIdeal p q hp hq)
  let S := hypersurface p hp
  let i := cubicSecondEquationCurveImmersion p q hp n hq
  obtain ⟨x, hx⟩ := hP
  have hpre : i ⁻¹' ({P.1} : Set S) = ({x} : Set X) := by
    ext y
    change i y = P.1 ↔ y = x
    constructor
    · intro hy
      exact i.isClosedEmbedding.injective (hy.trans hx.symm)
    · rintro rfl
      exact hx
  have hxclosed : IsClosed ({x} : Set X) := by
    have hclosed := P.2.preimage i.continuous
    rw [hpre] at hclosed
    exact hclosed
  let Q : closedPoints X := ⟨x, hxclosed⟩
  have hpoint : i Q.1 = P.1 := hx
  letI : IsIso (i.residueFieldMap Q.1) := isIso_residueFieldMap_of_surjectiveOnStalks i Q.1
  have hdegree := projectiveIntersection_originalClosedPoint_degree_eq_originalCubicImage_degree
    p q hp n hq Q
  rw [hpoint] at hdegree
  exact ⟨Q, hpoint, inferInstance, hdegree⟩

end PfaffianDescent.Coray
