import PfaffianDescent.CoraySameWitnessOriginalSharpOwnWordPoint
import PfaffianDescent.CorayJointModelEntireIncidenceExactDegreeDivisibility
import PfaffianDescent.CorayPrimeDegreeComponentOriginalSmallerPoint
import PfaffianDescent.CorayModelIncidenceOwnGenusWindow
import PfaffianDescent.CorayOriginalWholeIntersectionMaximalComponentDegree

/-! Actual original branch B from one model witness and strict own degree.
No chosen-model, incidence, regularity, cycle, word or section outcome premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Original SAME I/P/G and natural window produce an actual smaller
original cubic point from strict original degree, using exactly ONE model.
Its OWN lambda and proper rank-one branch are internally constructed. -/
theorem originalMinimalComponent_strictDegree_threeDivides_exists_smallerOriginalCubicPoint001
    {K Ω : Type u} [Field K] [CharZero K] [Field Ω] [Algebra K Ω]
    [IsGalois K Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 1 ≤ n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hI : I.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (P : closedPoints (scheme I))
    (G : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Ω))
    (hG : G.toIdeal ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))).toIdeal.minimalPrimes)
    (hPointCoprime : Nat.Coprime ((toBase I).residueDegree P.1) 3)
    (hLower : 1 + 3 * n.choose 2 ≤ (toBase I).residueDegree P.1)
    (hUpper : (toBase I).residueDegree P.1 < 1 + 3 * (n + 1).choose 2)
    (hPointLarge : 7 ≤ (toBase I).residueDegree P.1)
    (hThree : 3 ∣ actualCurveCoordinateHilbertDegree I)
    (hStrict : actualCurveCoordinateHilbertDegree I < 3 * n) :
    ∃ R : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 ∧
        (hypersurfaceToBase p hp).residueDegree R.1 < (toBase I).residueDegree P.1 := by
  classical
  have hPointWindow : 3 * n < (toBase I).residueDegree P.1 :=
    originalHilbertWindow_three_mul_lt n ((toBase I).residueDegree P.1)
      hLower hUpper hPointLarge
  have hGenusWindow : 3 * n * (n - 1) / 2 ≤ (toBase I).residueDegree P.1 := by
    have hTwice := coray_twice_chooseGenus_polynomial001 n
    omega
  obtain ⟨L, C, hC, hCG, hID, hclosed, hfiniteM, hfiniteP,
      hDmin, hGI, hField, hMu, hProductBound, hDegreeM, hDegreeK,
      hRank, hNuPositive, hSPositive, hSmall, hSCoprime, hRCoprime,
      hNuCoprime, hCycleMCoprime, hCycleKCoprime, hPoints, hSmaller⟩ :=
    originalMinimalGeometricComponent_exists_sameModel_sharpOwnWord_smallerOriginalPoint001
      p q hp hp0 n hn hq hnot I hI P G hG hPointCoprime hPointWindow hGenusWindow
  let M := homogeneousIdealStabilizerFixedField (K := K) C
  let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
  letI : C.toIdeal.IsPrime := hC.isPrime
  have hOwn : actualCurveCoordinateHilbertDegree D = actualCurveCoordinateHilbertDegree G :=
    homogeneousPrime_stabilizerModel_ownDegree_eq_geometricComponent001 L C G hCG
  have hProduct : Module.finrank K M * actualCurveCoordinateHilbertDegree D =
      actualCurveCoordinateHilbertDegree I := by
    rw [hField, hOwn]
    exact (originalSelectedMinimalPrime_geometricComponents_card_mul_degree_eq_originalDegree001
      p q hp hp0 n hn hq hnot I hI G hG).1
  have hRNot : ¬ 3 ∣ Module.finrank K M :=
    Nat.prime_three.coprime_iff_not_dvd.mp hRCoprime.symm
  have hOwnThree : 3 ∣ actualCurveCoordinateHilbertDegree D := by
    have h := hThree
    rw [← hProduct, Nat.prime_three.dvd_mul] at h
    exact h.resolve_left hRNot
  obtain ⟨lambda, hMuLambda⟩ := hOwnThree
  have hRPositive : 0 < Module.finrank K M := by
    by_contra h
    have hZero : Module.finrank K M = 0 := by omega
    apply hRNot
    rw [hZero]
    exact dvd_zero 3
  have hScaledStrict : Module.finrank K M * lambda < n := by
    have h := hStrict
    rw [← hProduct, hMuLambda, show Module.finrank K M * (3 * lambda) =
      3 * (Module.finrank K M * lambda) from by ring] at h
    omega
  have hBranch : 2 ≤ Module.finrank K M ∨
      (Module.finrank K M = 1 ∧ lambda < n) := by
    by_cases hR : 2 ≤ Module.finrank K M
    · exact Or.inl hR
    · have hOne : Module.finrank K M = 1 := by omega
      right
      refine ⟨hOne, ?_⟩
      simpa only [hOne, Nat.one_mul] using hScaledStrict
  have hNotFour : (toBase I).residueDegree P.1 ≠ 4 := by omega
  exact hSmaller lambda hMuLambda hBranch hLower hNotFour

/-- The literal WHOLE original intersection may be reducible or have a
single nonreduced component. Its actual nonintegrality supplies strict own
degree internally; all cycle/word geometry stays on the SAME chosen model. -/
theorem originalNonintegralWholeIntersection_component_threeDivides_exists_smallerOriginalCubicPoint001
    {K Ω : Type u} [Field K] [CharZero K] [Field Ω] [Algebra K Ω]
    [IsGalois K Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 1 ≤ n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hI : I.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (P : closedPoints (scheme I))
    (G : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Ω))
    (hG : G.toIdeal ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))).toIdeal.minimalPrimes)
    (hPointCoprime : Nat.Coprime ((toBase I).residueDegree P.1) 3)
    (hLower : 1 + 3 * n.choose 2 ≤ (toBase I).residueDegree P.1)
    (hUpper : (toBase I).residueDegree P.1 < 1 + 3 * (n + 1).choose 2)
    (hPointLarge : 7 ≤ (toBase I).residueDegree P.1)
    (hThree : 3 ∣ actualCurveCoordinateHilbertDegree I)
    (hNonIntegral : ¬ IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))) :
    ∃ R : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 ∧
        (hypersurfaceToBase p hp).residueDegree R.1 < (toBase I).residueDegree P.1 := by
  have hStrict := selectedOriginalWholeIntersection_nonintegral_minimalComponent_degree_lt001
    p q hp hp0 n hn hq hnot hNonIntegral I hI
  exact originalMinimalComponent_strictDegree_threeDivides_exists_smallerOriginalCubicPoint001
    p q hp hp0 n hn hq hnot I hI P G hG hPointCoprime hLower hUpper hPointLarge hThree hStrict

end PfaffianDescent.Coray
