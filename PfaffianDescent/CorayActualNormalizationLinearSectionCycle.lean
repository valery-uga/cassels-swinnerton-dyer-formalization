import PfaffianDescent.CorayActualRegularLinearSectionCycle
import PfaffianDescent.CorayRegularSupportedCurveCycleNormalizationLift

/-! The ACTUAL degree3*n hyperplane cycle on SAME canonical normalization.
Natural integral selected-curve hypotheses only: the original linear H,
literal nonzerodivisor, actual finite section, native multiplicities and
regular support are all constructed by the preceding leaves. ORIGINAL K
and full own residue degrees are retained. The actual native Q-stalk
comparison prerequisite is pending; this entire packet is SOURCE ONLY /
UNVERIFIED. No GI, rank-one constants or genus/RR conclusion is input. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory AllCharacteristics TopologicalSpace
open AllCharacteristics.HomogeneousProjective
open scoped BigOperators
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The original cubic--degree-n integral curve supplies, on its OWN
canonical normalization, an ACTUAL effective zero-cycle of FULL original-K
degree3*n. The witness lifts the actual hyperplane fundamental cycle with
exactly its original native multiplicities. -/
theorem projectiveIntersection_genericNormalization_exists_linearSection_cycle_degree_three_mul
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    ∃ w : EffectiveZeroCycle N, EffectiveZeroCycle.degree (nu ≫ toBase I) w = 3 * n := by
  classical
  intro I X N nu
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  obtain ⟨H, hH, hregular, z, hdegree, hsupport⟩ :=
    projectiveIntersection_exists_regular_linearSection_cycle_degree_three_mul p q hp hp0 n hq hnot
  obtain ⟨Q, hQ, hmaps, hliftdegree⟩ :=
    projectiveIntersection_genericNormalization_regularSupportedCycle_exists_degree_preserving_lift
      p q hp hp0 n hq hnot z hsupport
  exact ⟨∑ P : z.support, z P.1 • Finsupp.single (Q P) 1, hliftdegree.trans hdegree⟩

end PfaffianDescent.Coray
