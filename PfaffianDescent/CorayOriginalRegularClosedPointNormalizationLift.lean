import PfaffianDescent.CorayProperRegularClosedPointResidueLift
import PfaffianDescent.CorayFiniteSchemeGenericNormalization
import PfaffianDescent.CorayProjectiveIntersectionChartDimension
import Mathlib.RingTheory.Ideal.Height

/-! L2 actual canonical normalization point lift under EXPLICIT regularity
of the OWN original curve stalk. Actual dimension<=1, finite/proper nu and
its genuine generic-field lift are constructed. Original K is preserved.
SOURCE ONLY / UNVERIFIED. This does NOT select q regular or integral. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The OWN original intersection stalk has actual Krull dimension at most
one, through the original coordinate chart and its actual prime localization.
This root requires neither curve integrality nor point regularity. -/
theorem projectiveIntersection_original_stalk_ringKrullDim_le_one
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (P : scheme (projectiveIntersectionIdeal p q hp hq)) :
    ringKrullDim ((scheme (projectiveIntersectionIdeal p q hp hq)).presheaf.stalk P) ≤ 1 := by
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  obtain ⟨j, z, hz⟩ := exists_coordinate_chart I P
  let U := (chartι I j).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (chartι I j)
  have hPU : P ∈ U := ⟨z, hz⟩
  let e : Γ(X, U) ≃+* ChartRing I j :=
    ((IsOpenImmersion.ΓIsoTop (chartι I j)).symm ≪≫
      Scheme.ΓSpecIso (CommRingCat.of (ChartRing I j))).commRingCatIsoToRingEquiv
  have hdim : ringKrullDim Γ(X, U) ≤ 1 := by
    rw [ringKrullDim_eq_of_ringEquiv e]
    exact projectiveIntersection_chart_ringKrullDim_le_one p q hp hp0 n hq hnot j
  let J := (hU.primeIdealOf ⟨P, hPU⟩).asIdeal
  letI : J.IsPrime := (hU.primeIdealOf ⟨P, hPU⟩).isPrime
  letI : Algebra Γ(X, U) (X.presheaf.stalk P) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨P, hPU⟩
  letI : IsLocalization.AtPrime (X.presheaf.stalk P) J := hU.isLocalization_stalk ⟨P, hPU⟩
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height J (X.presheaf.stalk P)]
  exact (Ideal.height_le_ringKrullDim_of_ne_top (Ideal.IsPrime.ne_top' (I := J))).trans hdim

/-- On the integral selected-curve branch, a GIVEN regular original curve
point lifts to the SAME canonical normalization with relative residue degree1,
an actual residue-map isomorphism, and full degree over the ORIGINAL K.
Regularity is not derived from smoothness of the cubic or q interpolation.
No normalization residue-degree-one or generic-lift certificate is an input. -/
theorem projectiveIntersection_genericNormalization_regularClosedPoint_exists_degree_preserving_lift
    [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (P : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)))
    (hregular : IsRegularLocalRing
      ((scheme (projectiveIntersectionIdeal p q hp hq)).presheaf.stalk P.1)) :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    ∃ Q : closedPoints N,
      nu Q.1 = P.1 ∧ IsIso (nu.residueFieldMap Q.1) ∧
      nu.residueDegree Q.1 = 1 ∧
      (nu ≫ toBase I).residueDegree Q.1 = (toBase I).residueDegree P.1 := by
  classical
  intro I X N nu
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  letI : LocallyOfFiniteType (toBase I) := inferInstance
  letI : IsFinite nu := integralScheme_genericNormalization_isFinite X (toBase I)
  let f := X.fromSpecStalk (genericPoint X)
  have hdim : ringKrullDim (X.presheaf.stalk P.1) ≤ 1 :=
    projectiveIntersection_original_stalk_ringKrullDim_le_one p q hp hp0 n hq hnot P.1
  exact properMorph_regularClosedCurvePoint_exists_degree_preserving_closedPoint
    nu (toBase I) P hregular hdim f.toNormalization
    (Scheme.Hom.toNormalization_fromNormalization f)

end PfaffianDescent.Coray
