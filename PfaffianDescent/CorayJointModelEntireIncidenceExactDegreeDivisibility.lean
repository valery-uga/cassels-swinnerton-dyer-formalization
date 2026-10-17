import PfaffianDescent.CorayModelEntireIncidenceSupportPointDegree
import PfaffianDescent.CorayOriginalPrimeExactGeometricDegreeProduct

/-! SAME L/C/M/D and original P: exact OWN degree product and actual native
incidence divisibility. No small-count or desired divisibility outcome input. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The SAME original whole-ideal stabilizer contraction D_M extends to
C_L, which extends to the SAME geometric G_Omega. Both literal coefficient
identities yield actual OWN degree equality, without a degree certificate. -/
theorem homogeneousPrime_stabilizerModel_ownDegree_eq_geometricComponent001
    {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]
    (L : FiniteGaloisIntermediateField K Ω)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) L)) [C.toIdeal.IsPrime]
    (G : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Ω))
    (hCG : C.toIdeal.map (MvPolynomial.map (algebraMap L Ω)) = G.toIdeal) :
    let M := homogeneousIdealStabilizerFixedField (K := K) C
    let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
    actualCurveCoordinateHilbertDegree D = actualCurveCoordinateHilbertDegree G := by
  let M := homogeneousIdealStabilizerFixedField (K := K) C
  let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
  have hDL : D.toIdeal.map (MvPolynomial.map (algebraMap M L)) = C.toIdeal :=
    (homogeneousPrime_stabilizerFixedField_descends (K := K) C).2
  have hGC : actualCurveCoordinateHilbertDegree G = actualCurveCoordinateHilbertDegree C :=
    actualCurveCoordinateHilbertDegree_eq_coefficientExtension C G hCG
  have hCD : actualCurveCoordinateHilbertDegree C = actualCurveCoordinateHilbertDegree D :=
    actualCurveCoordinateHilbertDegree_eq_coefficientExtension D C hDL
  exact (hGC.trans hCD).symm

variable {K : Type u} [Field K] [CharZero K]

/-- Original p/q/minimal I and actual SAME geometric G/P construct the entire
joint model/cycle. Literal r*mu_D=mu_I and prime-three divisibility identities
are proved from native coefficient degrees and r*nu=d*s, with s the ACTUAL
kappa(P)-rank. Neither s<=2, r coprime3 nor 3|mu_D is supplied or asserted. -/
theorem originalMinimalGeometricComponent_exists_jointModel_entireIncidence_exactOriginalDegreeProduct_and_threeDivisibility001
    {Ω : Type u} [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 1 ≤ n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hI : I.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (P : closedPoints (scheme I))
    (G : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) Ω))
    (hG : G.toIdeal ∈
      (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))).toIdeal.minimalPrimes) :
    ∃ (L : FiniteGaloisIntermediateField K Ω)
      (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) L)),
      C.toIdeal ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K L))).toIdeal.minimalPrimes ∧
      C.toIdeal.map (MvPolynomial.map (algebraMap L Ω)) = G.toIdeal ∧
      let M := homogeneousIdealStabilizerFixedField (K := K) C
      let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
      ∃ hID : (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal ≤ D.toIdeal,
      let ep := (scheme I).fromSpecResidueField P.1
      let f := coefficientComponentToOriginal I D hID
      let a := pullback.snd ep f
      let c := pullback.fst ep f
      let pi := a ≫ toBase D
      ∃ hclosed : IsClosedImmersion a, ∃ hfinite : IsFinite pi, ∃ hfiniteP : IsFinite c,
        letI := hclosed
        letI := hfinite
        letI := hfiniteP
        let z := pushforwardClosedCycle a (finiteSchemeFundamentalCycle pi)
        D.toIdeal ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal.minimalPrimes ∧
          GeometricallyIntegral (toBase D) ∧
          Module.finrank K M = Nat.card (irreducibleComponents
            (scheme (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))))) ∧
          0 < actualCurveCoordinateHilbertDegree D ∧
          Module.finrank K M * actualCurveCoordinateHilbertDegree D ≤ 3 * n ∧
          EffectiveZeroCycle.degree (toBase D) z = finiteSchemeRank pi ∧
          EffectiveZeroCycle.degree (toBase D ≫ Spec.map (CommRingCat.ofHom (algebraMap K M))) z =
            Module.finrank K M * finiteSchemeRank pi ∧
          Module.finrank K M * finiteSchemeRank pi =
            (toBase I).residueDegree P.1 * (@finiteSchemeRank.{u} ((scheme I).residueField P.1) inferInstance (pullback ep f) c hfiniteP) ∧
          0 < finiteSchemeRank pi ∧ 0 < (@finiteSchemeRank.{u} ((scheme I).residueField P.1) inferInstance (pullback ep f) c hfiniteP) ∧
          (∀ Q ∈ z.support, f Q.1 = P.1) ∧
          (∀ Q ∈ z.support,
            (toBase I).residueDegree P.1 ∣
              Module.finrank K M * (toBase D).residueDegree Q.1 ∧
            (toBase I).residueDegree P.1 ≤
              Module.finrank K M * (toBase D).residueDegree Q.1) ∧
          Module.finrank K M * actualCurveCoordinateHilbertDegree D = actualCurveCoordinateHilbertDegree I ∧
          actualCurveCoordinateHilbertDegree D = actualCurveCoordinateHilbertDegree G ∧
          (3 ∣ actualCurveCoordinateHilbertDegree I ↔
            3 ∣ Module.finrank K M ∨ 3 ∣ actualCurveCoordinateHilbertDegree D) ∧
          (¬ 3 ∣ (toBase I).residueDegree P.1 →
            ((3 ∣ Module.finrank K M ∨ 3 ∣ finiteSchemeRank pi) ↔
              3 ∣ (@finiteSchemeRank.{u} ((scheme I).residueField P.1) inferInstance (pullback ep f) c hfiniteP))) := by
  obtain ⟨L, C, hCL, hCO, hID, hclosed, hfinite, hfiniteP,
      hDmin, hGI, hField, hMuPositive, hMuBound, hDegreeM, hDegreeK,
      hCount, hNuPositive, hSPositive, hPoints, hPointDegrees⟩ :=
    originalMinimalGeometricComponent_exists_jointModel_entireIncidence_supportPointDegreeLowerBounds001
      p q hp hp0 n hn hq hnot I hI P G hG
  let M := homogeneousIdealStabilizerFixedField (K := K) C
  let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
  letI : C.toIdeal.IsPrime := hCL.isPrime
  letI : Module.Finite K M := inferInstance
  let ep := (scheme I).fromSpecResidueField P.1
  let f := coefficientComponentToOriginal I D hID
  let a := pullback.snd ep f
  let c := pullback.fst ep f
  let pi := a ≫ toBase D
  letI := hclosed
  letI := hfinite
  letI := hfiniteP
  have hOwnDegree : actualCurveCoordinateHilbertDegree D = actualCurveCoordinateHilbertDegree G :=
    homogeneousPrime_stabilizerModel_ownDegree_eq_geometricComponent001 L C G hCO
  have hProduct : Module.finrank K M * actualCurveCoordinateHilbertDegree D =
      actualCurveCoordinateHilbertDegree I := by
    rw [hField, hOwnDegree]
    exact (originalSelectedMinimalPrime_geometricComponents_card_mul_degree_eq_originalDegree001
      p q hp hp0 n hn hq hnot I hI G hG).1
  have hDegreeDiv : 3 ∣ actualCurveCoordinateHilbertDegree I ↔
      3 ∣ Module.finrank K M ∨ 3 ∣ actualCurveCoordinateHilbertDegree D := by
    rw [← hProduct, Nat.prime_three.dvd_mul]
  have hCountNative : Module.finrank K M * finiteSchemeRank pi =
      (toBase I).residueDegree P.1 *
        (@finiteSchemeRank.{u} ((scheme I).residueField P.1) inferInstance (pullback ep f) c hfiniteP) := hCount
  have hIndexDiv : ¬ 3 ∣ (toBase I).residueDegree P.1 →
      ((3 ∣ Module.finrank K M ∨ 3 ∣ finiteSchemeRank pi) ↔
        3 ∣ (@finiteSchemeRank.{u} ((scheme I).residueField P.1) inferInstance (pullback ep f) c hfiniteP)) := by
    intro hd
    rw [← Nat.prime_three.dvd_mul, hCountNative, Nat.prime_three.dvd_mul]
    simp only [hd, false_or]
  exact ⟨L, C, hCL, hCO, hID, hclosed, hfinite, hfiniteP,
    hDmin, hGI, hField, hMuPositive, hMuBound, hDegreeM, hDegreeK,
    hCount, hNuPositive, hSPositive, hPoints, hPointDegrees,
    hProduct, hOwnDegree, hDegreeDiv, hIndexDiv⟩

end PfaffianDescent.Coray
