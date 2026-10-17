import PfaffianDescent.CorayModelIncidenceSharpDefect
import PfaffianDescent.CorayRankOneProperOwnGenusWindow
import PfaffianDescent.CoraySharpOwnWordDegreeWindows
import PfaffianDescent.CoraySharpOwnWordSectionCaseTransition
import PfaffianDescent.CorayCoefficientWordOriginalPoint
import PfaffianDescent.CorayModelEntireIncidenceSupportPointDegree
import PfaffianDescent.CorayComponentOwnNormalizationCycle
import PfaffianDescent.CoraySignedCycleWordDegreeSelection
import Mathlib.Algebra.CharP.Algebra
import AllCharacteristics.EffectiveCycleToZeroCycle

/-! Literal fixed-model whole incidence constructs its normalization word,
nonzero section, length cycle and smaller original cubic point. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial Opposite
open CategoryTheory.Abelian
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open scoped BigOperators
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- A fixed coefficient model consumes its actual field/incidence coprimality
and degree window. It constructs the ENTIRE literal incidence cycle, proves
its support regular, lifts it, constructs its OWN hyperplane cycle, encodes
the Bezout word, produces its nonzero section and obtains an original point.
No cycle, regularity, lift, word, section or desired point is supplied. -/
theorem fixedCoefficientModel_entireIncidence_sharpOwnWord_smallerOriginalPoint001
    {K M : Type u} [Field K] [CharZero K] [Field M] [Algebra K M] [Module.Finite K M]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hI : I.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (D : HomogeneousIdeal (homogeneousSubmodule (Fin 4) M))
    (hD : D.toIdeal ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal.minimalPrimes)
    [GeometricallyIntegral (toBase D)]
    (P : closedPoints (scheme I)) (lambda : ℕ) (hLambda : 1 ≤ lambda)
    (hMu : actualCurveCoordinateHilbertDegree D = 3 * lambda)
    (hScaledDegree : Module.finrank K M * lambda ≤ n)
    (hBranch : 2 ≤ Module.finrank K M ∨ (Module.finrank K M = 1 ∧ lambda < n))
    (hWindow : 1 + 3 * n.choose 2 ≤ (toBase I).residueDegree P.1)
    (hNotFour : (toBase I).residueDegree P.1 ≠ 4)
    (hFieldCoprime : Nat.Coprime (Module.finrank K M) 3) :
    let ep := (scheme I).fromSpecResidueField P.1
    let f := coefficientComponentToOriginal I D hD.le
    let piI := pullback.snd ep f ≫ toBase D
    ∀ hFinite : IsFinite piI,
      Nat.Coprime (@finiteSchemeRank.{u} M inferInstance (pullback ep f) piI hFinite) 3 →
      ∃ R : closedPoints (hypersurface p hp),
        Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 ∧
          (hypersurfaceToBase p hp).residueDegree R.1 < (toBase I).residueDegree P.1 := by
  classical
  letI : CharZero M := charZero_of_injective_algebraMap (algebraMap K M).injective
  letI : IsIntegral (scheme D) := GeometricallyIntegral.isIntegral_of_subsingleton (toBase D)
  let ep := (scheme I).fromSpecResidueField P.1
  let f := coefficientComponentToOriginal I D hD.le
  let a := pullback.snd ep f
  let piI := a ≫ toBase D
  dsimp only
  intro hFinite hIncidenceCoprime
  letI : IsFinite piI := hFinite
  obtain ⟨hClosed, hFiniteConstructed, hDegree, hPoints, hPointDegrees⟩ :=
    originalPointModelIncidence_entireCycle_supportPointDegreeLowerBounds001 I D hD.le P
  letI : IsClosedImmersion a := hClosed
  let z := pushforwardClosedCycle a (finiteSchemeFundamentalCycle piI)
  obtain ⟨hpM0, hSmoothM, hnotM, hDPair⟩ :=
    selectedOriginalMinimalComponent_coefficientMinimalPrime_originalPairInputs001
      p q hp hp0 n hq hnot I hI D hD
  letI : Smooth (hypersurfaceToBase (p.map (algebraMap K M)) (hp.map (algebraMap K M))) := hSmoothM
  let X := scheme D
  let PD : X := Classical.choice inferInstance
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let pi := nu ≫ toBase D
  let r := Module.finrank K M
  let d := (toBase I).residueDegree P.1
  let v := finiteSchemeRank piI
  have hStrict : r * (1 + 3 * lambda.choose 2) < d := by
    rcases hBranch with hR | ⟨hR, hProper⟩
    · exact coray_modelField_scaledOwnGenus_lt_originalDegree001
        r lambda n d hR hLambda hScaledDegree hWindow
    · exact coray_modelField_scaledOwnGenus_lt_originalDegree_rankOne_proper001
        r lambda n d hR hLambda hProper hWindow
  have hRegular : ∀ Q ∈ z.support, IsRegularLocalRing (X.presheaf.stalk Q.1) := by
    intro Q hQ
    have hDefect : Module.finrank M (SchemeModuleGlobalSectionsOver (toBase D)
        (genericNormalizationQuotientSheaf X)) ≤ 1 + 3 * lambda.choose 2 :=
      selectedMinimalComponent_geometricallyIntegral_genericNormalization_sharpDefect_bound001
        (p.map (algebraMap K M)) (q.map (algebraMap K M)) (hp.map (algebraMap K M)) hpM0
        n (hq.map (algebraMap K M)) hnotM D hDPair Q lambda hMu
    by_contra hSingular
    have hContribution : (toBase D).residueDegree Q.1 ≤
        Module.finrank M (SchemeModuleGlobalSectionsOver (toBase D)
          (genericNormalizationQuotientSheaf X)) :=
      selectedPrimeComponent_nonregular_originalClosedPoint_degree_le_globalDefect
        (p.map (algebraMap K M)) (q.map (algebraMap K M)) (hp.map (algebraMap K M)) hpM0
        n (hq.map (algebraMap K M)) hnotM D hDPair.le hDPair.isPrime Q hSingular
    have hBound : d ≤ r * (1 + 3 * lambda.choose 2) :=
      (hPointDegrees Q hQ).2.trans (Nat.mul_le_mul_left r (hContribution.trans hDefect))
    exact (not_lt_of_ge hBound) hStrict
  obtain ⟨R, _hRInjective, _hRMaps, hLiftDegree⟩ :=
    selectedMinimalComponent_genericNormalization_regularSupportedCycle_exists_degree_preserving_lift
      (p.map (algebraMap K M)) (q.map (algebraMap K M)) (hp.map (algebraMap K M)) hpM0
      n (hq.map (algebraMap K M)) hnotM D hDPair z hRegular
  let zN : EffectiveZeroCycle N := ∑ Q : z.support, z Q.1 • Finsupp.single (R Q) 1
  have hDegreeN : EffectiveZeroCycle.degree pi zN = v := hLiftDegree.trans hDegree
  obtain ⟨zH, hDegreeH, _hOwnBound⟩ :=
    selectedMinimalComponent_genericNormalization_exists_own_degree_cycle
      (p.map (algebraMap K M)) (q.map (algebraMap K M)) (hp.map (algebraMap K M)) hpM0
      n (hq.map (algebraMap K M)) hnotM D hDPair
  have hDegreeHNative : EffectiveZeroCycle.degree pi zH = 3 * lambda := hDegreeH.trans hMu
  let delta := Nat.gcd v (3 * lambda)
  have hVPositive : 0 < v := by
    by_contra h
    have hZero : v = 0 := by omega
    have h := hIncidenceCoprime
    change Nat.Coprime v 3 at h
    rw [hZero] at h
    norm_num at h
  have hDelta : 0 < delta := Nat.gcd_pos_of_pos_left (3 * lambda) hVPositive
  have hDeltaPrime : ¬ 3 ∣ delta := by
    intro h
    have hVCoprime : Nat.Coprime v 3 := hIncidenceCoprime
    exact (Nat.prime_three.coprime_iff_not_dvd.mp hVCoprime.symm)
      (dvd_trans h (Nat.gcd_dvd_left v (3 * lambda)))
  have hDeltaDegree : delta ∣ 3 * lambda := Nat.gcd_dvd_right v (3 * lambda)
  have hTheta : ∃ theta : ℕ, 0 < theta ∧ delta ∣ theta ∧ ¬ 3 ∣ theta ∧
      1 + 3 * lambda.choose 2 ≤ theta ∧ r * theta < d := by
    rcases hBranch with hR | ⟨hR, hProper⟩
    · exact coray_scaledSharpWordWindow_exists_multiple_smaller_originalDegree001
        r lambda n d delta hR hLambda hScaledDegree hWindow hNotFour hDelta hDeltaPrime hDeltaDegree
    · obtain ⟨theta, hPositive, hMultiple, hPrime, hLow, hHigh⟩ :=
        coray_properOwnSharpWordWindow_exists_multiple_smaller_originalDegree001
          lambda n d delta hLambda hProper hWindow hDelta hDeltaPrime hDeltaDegree
      refine ⟨theta, hPositive, hMultiple, hPrime, hLow, ?_⟩
      simpa only [r, hR, Nat.one_mul] using hHigh
  obtain ⟨theta, _hPositive, hMultiple, hPrime, hLow, hHigh⟩ := hTheta
  have hCycleD : ZeroCycle.degree pi zN.toZeroCycle = (v : ℤ) :=
    (EffectiveZeroCycle.degree_toZeroCycle pi zN).trans (congrArg (fun t : ℕ => (t : ℤ)) hDegreeN)
  have hCycleH : ZeroCycle.degree pi zH.toZeroCycle = ((3 * lambda : ℕ) : ℤ) :=
    (EffectiveZeroCycle.degree_toZeroCycle pi zH).trans (congrArg (fun t : ℕ => (t : ℤ)) hDegreeHNative)
  obtain ⟨ops, hWeight⟩ := exists_signedPointTensorOperations_weight_eq_multiple_gcd
    pi v (3 * lambda) zN.toZeroCycle zH.toZeroCycle hCycleD hCycleH theta hMultiple
  have hWeightBound : ((1 + 3 * lambda.choose 2 : ℕ) : ℤ) ≤
      schemeModuleSignedClosedPointTensorWeightSum pi ops +
        (Module.finrank M (SchemeModuleGlobalSectionsOver (toBase D)
          (genericNormalizationQuotientSheaf X)) : ℤ) := by
    rw [hWeight]
    have hLowInt : ((1 + 3 * lambda.choose 2 : ℕ) : ℤ) ≤ (theta : ℤ) := by exact_mod_cast hLow
    have hNonnegative : (0 : ℤ) ≤
        (Module.finrank M (SchemeModuleGlobalSectionsOver (toBase D)
          (genericNormalizationQuotientSheaf X)) : ℤ) := by positivity
    omega
  obtain ⟨s, hs⟩ :=
    selectedMinimalComponent_genericNormalization_signedWord_exists_nonzero_section_of_sharp_weight_add_defect001
      (p.map (algebraMap K M)) (q.map (algebraMap K M)) (hp.map (algebraMap K M)) hpM0
      n (hq.map (algebraMap K M)) hnotM D hDPair PD lambda hMu ops hWeightBound
  have hThetaCoprime : Nat.Coprime theta 3 :=
    (Nat.prime_three.coprime_iff_not_dvd.mpr hPrime).symm
  obtain ⟨R0, hR0Coprime, hR0Bound⟩ :=
    selectedOriginalComponent_coefficientModel_wordSection_originalCubic_point001
      p q hp hp0 n hq hnot I hI D hD hFieldCoprime ops theta hWeight hThetaCoprime s hs
  exact ⟨R0, hR0Coprime, hR0Bound.trans_lt hHigh⟩

end PfaffianDescent.Coray
