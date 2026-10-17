import PfaffianDescent.CorayProjectiveOriginalPointStrictRegularity
import PfaffianDescent.CorayOriginalRegularClosedPointNormalizationLift
import PfaffianDescent.CorayActualNormalizationLinearSectionCycle

/-! Natural strict GI original-curve inputs construct BOTH actual
normalization degrees: the OWN lifted original point, and the OWN degree3*n
hyperplane cycle. Regularity, normalization residue preservation and the
hyperplane cycle are not certificates supplied by the caller. The strict
regularity and hyperplane-cycle prerequisites are pending actual root checks.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory AllCharacteristics TopologicalSpace
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The manuscript's genuine GI strict degree case constructs the OWN
normalization lift with ALL actual residue-map conclusions and the native
multiplicity degree3*n hyperplane cycle over the ORIGINAL K. -/
theorem projectiveIntersection_geometricallyIntegral_strictOriginalPoint_exists_ownLift_and_hyperplaneCycle
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [GeometricallyIntegral (toBase (projectiveIntersectionIdeal p q hp hq))]
    (P : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)))
    (hdegree : 1 + 3 * n * (n - 1) / 2 <
      (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1) :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton (toBase I)
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let pi := nu ≫ toBase I
    ∃ Q : closedPoints N,
      nu Q.1 = P.1 ∧ IsIso (nu.residueFieldMap Q.1) ∧
      nu.residueDegree Q.1 = 1 ∧ pi.residueDegree Q.1 = (toBase I).residueDegree P.1 ∧
      ∃ zH : EffectiveZeroCycle N, EffectiveZeroCycle.degree pi zH = 3 * n := by
  classical
  intro I X N nu pi
  letI : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton (toBase I)
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  have hregular := projectiveIntersection_geometricallyIntegral_originalClosedPoint_isRegularLocalRing_of_degree_gt
    p q hp hp0 n hn hq hnot P hdegree
  obtain ⟨Q, hQpoint, hQiso, hQrelative, hQground⟩ :=
    projectiveIntersection_genericNormalization_regularClosedPoint_exists_degree_preserving_lift
      p q hp hp0 n hq hnot P hregular
  obtain ⟨zH, hHdegree⟩ :=
    projectiveIntersection_genericNormalization_exists_linearSection_cycle_degree_three_mul
      p q hp hp0 n hq hnot
  exact ⟨Q, hQpoint, hQiso, hQrelative, hQground, zH, hHdegree⟩

end PfaffianDescent.Coray
