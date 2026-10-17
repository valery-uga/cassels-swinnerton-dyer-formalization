import PfaffianDescent.CorayOwnComponentWordSection
import PfaffianDescent.CorayPerfectOwnNormalizationNonzeroWordCokernel
import PfaffianDescent.CorayPerfectOwnNormalizationNonzeroWordCokernelHOneZero
import PfaffianDescent.SchemeModuleFinitePointSequenceBalance
import PfaffianDescent.CorayEffectiveCyclePointBound
import PfaffianDescent.CorayCubicSecondEquationActualCurveUnit

/-! Source-only: actual OWN signed-word cokernel Euler gives actual native
length-cycle degree equal to signed weight, and a bounded original cubic point. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual OWN native length cycle has EXACT signed-word weight. The native
short-exact section sequence and its actual H1-zero cokernel give the rank
balance; full normalization constants cancel rather than being set to one. -/
theorem selectedMinimalComponent_genericNormalization_nonzeroWordSection_lengthCycle_degree_eq_weight
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (P : scheme C) :
    letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hmin.isPrime P
    let X := scheme C
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let pi := nu ≫ toBase C
    ∀ ops : List (closedPoints N × Bool),
      let W := schemeModuleIteratedSignedClosedPointTensor (SheafOfModules.unit N.ringCatSheaf) ops
      ∀ (s : W.val.obj (op ⊤)), s ≠ 0 →
        let Q : N.Modules := cokernel (schemeModuleTopSectionHom W s)
        let support := schemeModuleStalkSupport Q
        ∃ (hsupport : support.Finite) (hpoints : ∀ x ∈ support, IsClosed ({x} : Set N)),
          (EffectiveZeroCycle.degree pi
            (schemeModuleFiniteClosedSupportLengthCycle Q support hsupport hpoints) : ℤ) =
              schemeModuleSignedClosedPointTensorWeightSum pi ops := by
  letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hmin.isPrime P
  let X := scheme C
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let pi := nu ≫ toBase C
  let ON : N.Modules := SheafOfModules.unit N.ringCatSheaf
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K N.Modules := schemeModulesLinearOver pi
  have h0 : Module.Finite K (SchemeModuleOpenSectionsOver pi ON ⊤) :=
    (perfectField_homogeneousPrime_genericNormalization_originalConstants_finite_and_finrank_dvd
      C hmin.isPrime P).2.2.1
  have h1 : Module.Finite K (schemeModuleCohomology N ON 1) :=
    perfectField_selectedProjectivePrimeComponent_genericNormalization_unit_cohomology_one_finite_native
      p q hp hp0 n hq hnot C hmin.le hmin.isPrime P
  dsimp only
  intro ops s hs
  let W := schemeModuleIteratedSignedClosedPointTensor ON ops
  let Q : N.Modules := cokernel (schemeModuleTopSectionHom W s)
  let S := ShortComplex.cokernelSequence (schemeModuleTopSectionHom W s)
  obtain ⟨hSupport, hpoints, _hLengths, hQfinite, hDegree⟩ :=
    perfectField_selectedProjectiveMinimalComponent_normalization_nonzeroWordSection_cokernel_finiteHZero_and_lengthCycle
      p q hp hp0 n hq hnot C hmin P ops s hs
  have hMon := perfectField_selectedProjectiveMinimalComponent_normalization_nonzeroWordSection_mono_and_genericZero
    p q hp hp0 n hq hnot C hmin P ops s hs
  have hShort : S.ShortExact := hMon.2.2.1
  have hQzero : Subsingleton (schemeModuleCohomology N Q 1) :=
    perfectField_selectedProjectiveMinimalComponent_normalization_nonzeroWordSection_cokernel_cohomology_one_subsingleton
      p q hp hp0 n hq hnot C hmin P ops s hs
  obtain ⟨_hWfinite0, _hWfinite1, hBalance⟩ :=
    schemeModuleShortExact_finite_second_and_h0_h1_balance pi S hShort h0 h1 hQfinite hQzero
  have hBalanceNative :
      Module.finrank K (SchemeModuleOpenSectionsOver pi W ⊤) +
        Module.finrank K (schemeModuleCohomology N ON 1) =
      Module.finrank K (SchemeModuleOpenSectionsOver pi ON ⊤) +
        Module.finrank K (SchemeModuleOpenSectionsOver pi Q ⊤) +
        Module.finrank K (schemeModuleCohomology N W 1) := hBalance
  obtain ⟨_hRank, _h0Word, _h1Word, hChange⟩ :=
    selectedMinimalComponent_genericNormalization_signedWord_finite_and_euler_change
      p q hp hp0 n hq hnot C hmin P ops
  have hChangeNative :
      (Module.finrank K (SchemeModuleOpenSectionsOver pi W ⊤) : ℤ) -
        (Module.finrank K (schemeModuleCohomology N W 1) : ℤ) =
      (Module.finrank K (SchemeModuleOpenSectionsOver pi ON ⊤) : ℤ) -
        (Module.finrank K (schemeModuleCohomology N ON 1) : ℤ) +
        schemeModuleSignedClosedPointTensorWeightSum pi ops := hChange
  have hQweight : (Module.finrank K (SchemeModuleOpenSectionsOver pi Q ⊤) : ℤ) =
      schemeModuleSignedClosedPointTensorWeightSum pi ops := by omega
  refine ⟨hSupport, hpoints, ?_⟩
  exact (congrArg (fun d : ℕ => (d : ℤ)) hDegree).trans hQweight

/-- SAME actual OWN word section produces a prime-to-three point on the
ORIGINAL cubic of degree at most its actual signed weight. Every native cycle,
finite map and original-K degree square is constructed; GI is never assumed. -/
theorem selectedMinimalComponent_ownWordSection_originalCubic_imagePoint_degree_le
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (P : scheme C) :
    letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hmin.isPrime P
    let X := scheme C
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let pi := nu ≫ toBase C
    ∀ (ops : List (closedPoints N × Bool)) (theta : ℕ),
      schemeModuleSignedClosedPointTensorWeightSum pi ops = (theta : ℤ) →
      ¬ 3 ∣ theta →
      let W := schemeModuleIteratedSignedClosedPointTensor (SheafOfModules.unit N.ringCatSheaf) ops
      ∀ (s : W.val.obj (op ⊤)), s ≠ 0 →
        ∃ R : closedPoints (hypersurface p hp),
          Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 ∧
            (hypersurfaceToBase p hp).residueDegree R.1 ≤ theta := by
  classical
  letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hmin.isPrime P
  let X := scheme C
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let pi := nu ≫ toBase C
  dsimp only
  intro ops theta hweight hprime s hs
  let W := schemeModuleIteratedSignedClosedPointTensor (SheafOfModules.unit N.ringCatSheaf) ops
  let Q : N.Modules := cokernel (schemeModuleTopSectionHom W s)
  let support := schemeModuleStalkSupport Q
  obtain ⟨hSupport, hpoints, hCycleDegree⟩ :=
    selectedMinimalComponent_genericNormalization_nonzeroWordSection_lengthCycle_degree_eq_weight
      p q hp hp0 n hq hnot C hmin P ops s hs
  let z := schemeModuleFiniteClosedSupportLengthCycle Q support hSupport hpoints
  have hDegreeInt : (EffectiveZeroCycle.degree pi z : ℤ) = (theta : ℤ) :=
    hCycleDegree.trans hweight
  have hDegree : EffectiveZeroCycle.degree pi z = theta := by exact_mod_cast hDegreeInt
  let I := projectiveIntersectionIdeal p q hp hq
  let j := schemeQuotientMap I C hmin.le
  let i := cubicSecondEquationCurveImmersion p q hp n hq
  let rho := nu ≫ (j ≫ i)
  letI : IsClosedImmersion j := schemeQuotientMap_closedImmersion I C hmin.le
  letI : IsFinite nu := integralScheme_genericNormalization_isFinite X (toBase C)
  letI : IsFinite rho := by dsimp only [rho]; infer_instance
  have hground : rho ≫ hypersurfaceToBase p hp = pi := by
    dsimp only [rho, pi]
    rw [Category.assoc, Category.assoc, cubicSecondEquationCurveImmersion_toBase,
      schemeQuotientMap_toBase]
  have hz : EffectiveZeroCycle.degree (rho ≫ hypersurfaceToBase p hp) z = theta := by
    rw [hground]
    exact hDegree
  have hcycleCop : Nat.Coprime (EffectiveZeroCycle.degree (rho ≫ hypersurfaceToBase p hp) z) 3 := by
    rw [hz]
    exact (Nat.prime_three.coprime_iff_not_dvd.mpr hprime).symm
  obtain ⟨R_N, hRcop, hRbound⟩ := proper_effectiveCycle_coprime_degree_has_bounded_imagePoint
    rho (hypersurfaceToBase p hp) z hcycleCop
  exact ⟨universallyClosedPointMap rho R_N, hRcop, hRbound.trans_eq hz⟩

end PfaffianDescent.Coray
