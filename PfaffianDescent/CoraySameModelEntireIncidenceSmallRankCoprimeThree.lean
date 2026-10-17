import PfaffianDescent.CorayEntireIncidenceSmallRankCoprimeArithmetic
import PfaffianDescent.CorayFixedStabilizerModelUnitCokernelFiniteSupport
import PfaffianDescent.CorayLiteralModelLocalGlobalGluingInequality
import PfaffianDescent.CorayModelIncidencePositive

/-! SAME original p/q/I/G/P and ONCE-constructed actual full model/cycle:
finite support and actual gluing inequality force small native residue rank. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Construct ONCE the actual joint model/full incidence cycle of SAME I/G/P,
then derive s<=2 and coprimality of model-field/whole-incidence degrees from
its genuine finite gluing support. No outcome/finite support/whole-I GI premise.
The original numeric degree window is explicit, not presumed in every branch. -/
theorem originalMinimalGeometricComponent_exists_sameModel_entireIncidence_smallRank_coprimeThree001
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
            (∀ Q ∈ z.support, f Q.1 = P.1) := by
  classical
  letI : I.toIdeal.IsPrime := hI.isPrime
  have hIrel := selectedProjectiveMinimalComponent_homogeneous_relevant
    p q hp hp0 n hq hnot I hI
  obtain ⟨L, C, hC, hCG, hID, hclosed, hfiniteM, hfiniteP,
      hDmin, hGI, hField, hMu, hProduct, hDegreeM, hDegreeK,
      hRank, hNuPositive, hSPositive, hPoints⟩ :=
    originalMinimalGeometricComponent_exists_jointModel_entire_incidence_positive_rank_count
      p q hp hp0 n hn hq hnot I hI P G hG
  let M := homogeneousIdealStabilizerFixedField (K := K) C
  let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
  letI : Module.Finite K M := inferInstance
  letI : GeometricallyIntegral (toBase D) := hGI
  let ep := (scheme I).fromSpecResidueField P.1
  let f := coefficientComponentToOriginal I D hID
  let a := pullback.snd ep f
  let c := pullback.fst ep f
  let pi := a ≫ toBase D
  letI : IsClosedImmersion a := hclosed
  letI : IsFinite pi := hfiniteM
  letI : IsFinite c := hfiniteP
  let z := pushforwardClosedCycle a (finiteSchemeFundamentalCycle pi)
  let r := Module.finrank K M
  let nu := finiteSchemeRank pi
  let d := (toBase I).residueDegree P.1
  let s := finiteSchemeRank c
  have hR : r ≤ 3 * n :=
    modelFieldDegree_le_cubicDegree_of_positiveOwnDegree001 r
      (actualCurveCoordinateHilbertDegree D) n hMu hProduct
  have hCO : (C.toIdeal.map (MvPolynomial.map (algebraMap L Ω))).IsPrime :=
    hCG.symm ▸ hG.isPrime
  obtain ⟨_hIDSupport, T, hTClosed, hTFinite, hTPoints, hSupport⟩ :=
    selectedOriginalPrime_fixedStabilizerModel_unitCokernel_exists_finiteClosedSupport001
      p q hp hp0 n hq hnot I hI hIrel C hC hCO
  have hSupportSame : schemeModuleStalkSupport
      (cokernel (C := (scheme I).Modules)
        (SheafOfModules.unitToPushforwardObjUnit
          (coefficientComponentToOriginal I D hDmin.le).toRingCatSheafHom)) ⊆ T := hSupport
  have hnPositive : 0 < n := by omega
  obtain ⟨hfinitePIneq, hInequality⟩ :=
    selectedOriginalPrime_actualCoefficientModel_localGlobalIncidence_gluingInequality
      (K := K) (M := M) p q hp hp0 n hnPositive hq hnot I hI D hDmin P
      T hTFinite hTPoints hSupportSame
  have hLocalGlobal : d * (s - 1) ≤ r + 3 * n * (n - 1) / 2 := hInequality
  have hCount : r * nu = d * s := hRank
  have hSPos : 0 < s := hSPositive
  obtain ⟨hSmall, hSCoprime, hRCoprime, hNuCoprime, hProductCoprime⟩ :=
    entireIncidenceRank_small_and_modelDegrees_coprime_three001
      r nu d s (3 * n * (n - 1) / 2) n
      hSPos hCount hLocalGlobal hR hPointLarge hGenusWindow hPointCoprime
  have hCycleMCoprime : Nat.Coprime (EffectiveZeroCycle.degree (toBase D) z) 3 := by
    rw [hDegreeM]
    exact hNuCoprime
  have hCycleKCoprime : Nat.Coprime (EffectiveZeroCycle.degree
      (toBase D ≫ Spec.map (CommRingCat.ofHom (algebraMap K M))) z) 3 := by
    rw [hDegreeK]
    exact hProductCoprime
  exact ⟨L, C, hC, hCG, hID, hclosed, hfiniteM, hfiniteP,
    hDmin, hGI, hField, hMu, hProduct, hDegreeM, hDegreeK,
    hRank, hNuPositive, hSPositive, hSmall, hSCoprime, hRCoprime,
    hNuCoprime, hCycleMCoprime, hCycleKCoprime, hPoints⟩

end PfaffianDescent.Coray
