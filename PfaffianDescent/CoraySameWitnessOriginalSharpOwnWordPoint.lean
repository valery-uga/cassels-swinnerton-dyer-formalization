import PfaffianDescent.CorayFixedCoefficientModelEntireIncidenceSharpWordPoint
import PfaffianDescent.CoraySameModelEntireIncidenceSmallRankCoprimeThree

/-! A SINGLE actual L/C/M/D/whole-cycle witness yields the sharp word point. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra

/-- SAME original I/G/P constructs the model ONCE. All its field/incidence
coprimalities and every geometric cycle/section required for a smaller original
point are constructed. The degree3lambda, proper/field-rank branch, lower
window and degree-four exception remain explicit on THAT SAME witness. -/
theorem originalMinimalGeometricComponent_exists_sameModel_sharpOwnWord_smallerOriginalPoint001
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
    (hPointLarge : 3 * n < (toBase I).residueDegree P.1)
    (hGenusWindow : 3 * n * (n - 1) / 2 ≤ (toBase I).residueDegree P.1) :
    ∃ (L : FiniteGaloisIntermediateField K Ω)
      (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) L)),
    ∃ hC : C.toIdeal ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K L))).toIdeal.minimalPrimes,
    ∃ hCG : C.toIdeal.map (MvPolynomial.map (algebraMap L Ω)) = G.toIdeal,
      let M := homogeneousIdealStabilizerFixedField (K := K) C
      let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
      ∃ hID : (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal ≤ D.toIdeal,
        let ep := (scheme I).fromSpecResidueField P.1
        let f := coefficientComponentToOriginal I D hID
        let a := pullback.snd ep f
        let c := pullback.fst ep f
        let pi := a ≫ toBase D
        ∃ hclosed : IsClosedImmersion a, ∃ hfiniteM : IsFinite pi, ∃ hfiniteP : IsFinite c,
          letI := hclosed
          letI := hfiniteM
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
              (toBase I).residueDegree P.1 * finiteSchemeRank c ∧
            0 < finiteSchemeRank pi ∧ 0 < finiteSchemeRank c ∧ finiteSchemeRank c ≤ 2 ∧
            Nat.Coprime (finiteSchemeRank c) 3 ∧ Nat.Coprime (Module.finrank K M) 3 ∧
            Nat.Coprime (finiteSchemeRank pi) 3 ∧
            Nat.Coprime (EffectiveZeroCycle.degree (toBase D) z) 3 ∧
            Nat.Coprime (EffectiveZeroCycle.degree
              (toBase D ≫ Spec.map (CommRingCat.ofHom (algebraMap K M))) z) 3 ∧
            (∀ Q ∈ z.support, f Q.1 = P.1) ∧
            (∀ lambda : ℕ, actualCurveCoordinateHilbertDegree D = 3 * lambda →
              (2 ≤ Module.finrank K M ∨ (Module.finrank K M = 1 ∧ lambda < n)) →
              1 + 3 * n.choose 2 ≤ (toBase I).residueDegree P.1 →
              (toBase I).residueDegree P.1 ≠ 4 →
              ∃ R : closedPoints (hypersurface p hp),
                Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 ∧
                  (hypersurfaceToBase p hp).residueDegree R.1 < (toBase I).residueDegree P.1) := by
  classical
  obtain ⟨L, C, hC, hCG, hID, hclosed, hfiniteM, hfiniteP,
      hDmin, hGI, hField, hMu, hProduct, hDegreeM, hDegreeK,
      hRank, hNuPositive, hSPositive, hSmall, hSCoprime, hRCoprime,
      hNuCoprime, hCycleMCoprime, hCycleKCoprime, hPoints⟩ :=
    originalMinimalGeometricComponent_exists_sameModel_entireIncidence_smallRank_coprimeThree001
      p q hp hp0 n hn hq hnot I hI P G hG hPointCoprime hPointLarge hGenusWindow
  let M := homogeneousIdealStabilizerFixedField (K := K) C
  let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
  letI : Module.Finite K M := inferInstance
  letI : GeometricallyIntegral (toBase D) := hGI
  let ep := (scheme I).fromSpecResidueField P.1
  let f := coefficientComponentToOriginal I D hID
  let a := pullback.snd ep f
  let pi := a ≫ toBase D
  letI : IsFinite pi := hfiniteM
  refine ⟨L, C, hC, hCG, hID, hclosed, hfiniteM, hfiniteP,
    hDmin, hGI, hField, hMu, hProduct, hDegreeM, hDegreeK,
    hRank, hNuPositive, hSPositive, hSmall, hSCoprime, hRCoprime,
    hNuCoprime, hCycleMCoprime, hCycleKCoprime, hPoints, ?_⟩
  intro lambda hMuLambda hBranch hWindow hNotFour
  have hLambda : 1 ≤ lambda := by
    have h := hMu
    rw [hMuLambda] at h
    omega
  have hScaledDegree : Module.finrank K M * lambda ≤ n := by
    have h := hProduct
    rw [hMuLambda, show Module.finrank K M * (3 * lambda) =
      3 * (Module.finrank K M * lambda) from by ring] at h
    omega
  exact fixedCoefficientModel_entireIncidence_sharpOwnWord_smallerOriginalPoint001
    p q hp hp0 n hq hnot I hI D hDmin P lambda hLambda hMuLambda
    hScaledDegree hBranch hWindow hNotFour hRCoprime hfiniteM hNuCoprime

end PfaffianDescent.Coray
