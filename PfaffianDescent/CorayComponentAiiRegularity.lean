import PfaffianDescent.CorayClosedComponentIntrinsicH1Bound
import PfaffianDescent.CorayComponentOwnNormalizationCycle
import PfaffianDescent.CorayPerfectOwnNormalizationEuler
import PfaffianDescent.CorayNormalizationConstantsHyperplaneCycle
import PfaffianDescent.CorayOwnProjectiveComponentNormalizationQuotientFinite
import PfaffianDescent.CorayIntegralAiiRegularPoint
import PfaffianDescent.CorayPrimeDegreeComponentOriginalSmallerPoint

/-! Source-only: OWN component full-constants Euler and actual global defect
transport give regularity at the SAME original point in A(ii). -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual global normalization defect of the SAME selected prime component
identifies with its literal original-K affine integral-closure quotient.
All support, affine choice, finite sections and scalar comparison are derived. -/
theorem selectedPrimeComponent_genericNormalizationQuotient_exists_globalSectionsEquiv_affineDefect
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal)
    (hprime : C.toIdeal.IsPrime) (x : scheme C) :
    letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hprime x
    ∃ (U : (scheme C).affineOpens) (hU : Nonempty U.1),
      letI : Nonempty U.1 := hU
      x ∈ U.1 ∧ Nonempty
        (SchemeModuleGlobalSectionsOver (toBase C)
          (genericNormalizationQuotientSheaf (scheme C)) ≃ₗ[K]
          (ModuleCat.restrictScalars (schemeOpenBaseRingHom (toBase C) U.1)).obj
            (ModuleCat.of Γ(scheme C, U.1)
              (localNormalizationDefect Γ(scheme C, U.1) (scheme C).functionField))) := by
  letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hprime x
  let X := scheme C
  let pi := toBase C
  let Q := genericNormalizationQuotientSheaf X
  have hfiniteSupport :=
    (selectedProjectivePrimeComponent_genericNormalizationQuotient_finite_sections_and_support
      p q hp hp0 n hq hnot C hIC hprime x).2
  obtain ⟨U, hnonempty, hsU, hxU⟩ :=
    projectiveModule_exists_affineOpen_containing_support_and_point C Q hfiniteSupport x
  letI : Nonempty U.1 := hnonempty
  have hclosed : IsClosed (schemeModuleStalkSupport Q) :=
    integralScheme_genericNormalizationQuotient_stalkSupport_isClosed X pi
  let eGlobal : SchemeModuleGlobalSectionsOver pi Q ≃ₗ[K]
      SchemeModuleOpenSectionsOver pi Q U.1 :=
    schemeModule_groundGlobalSectionsEquiv_of_closedSupport_subset
      pi Q U.1 (schemeModuleStalkSupport Q) hclosed (Set.Subset.rfl) hsU
  let D := (ModuleCat.restrictScalars (schemeOpenBaseRingHom pi U.1)).obj
    (ModuleCat.of Γ(X, U.1) (localNormalizationDefect Γ(X, U.1) X.functionField))
  let eAffine : SchemeModuleOpenSectionsOver pi Q U.1 ≃ₗ[K] D :=
    (genericNormalizationQuotientSheaf_groundAffineSectionsIso K X pi U.1 U.2).toLinearEquiv
  exact ⟨U, hnonempty, hxU, ⟨eGlobal.trans eAffine⟩⟩

/-- Three dividing the SAME component normalization's full constants rank
forces OWN global defect at least twice the actual original-K point degree.
The genuine closed lift and native affine evaluation are constructed. -/
theorem selectedPrimeComponent_three_constants_globalDefect_ge_twice_point_degree
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal)
    (hprime : C.toIdeal.IsPrime) (P : closedPoints (scheme C))
    (hcop : Nat.Coprime ((toBase C).residueDegree P.1) 3) :
    letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hprime P.1
    let X := scheme C
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    3 ∣ Module.finrank K (SchemeModuleOpenSectionsOver (nu ≫ toBase C)
      (SheafOfModules.unit N.ringCatSheaf) ⊤) →
      2 * (toBase C).residueDegree P.1 ≤
        Module.finrank K (SchemeModuleGlobalSectionsOver (toBase C)
          (genericNormalizationQuotientSheaf X)) := by
  classical
  letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hprime P.1
  let X := scheme C
  let pi := toBase C
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let G := SchemeModuleGlobalSectionsOver pi (genericNormalizationQuotientSheaf X)
  letI : Module.Finite K G :=
    (selectedProjectivePrimeComponent_genericNormalizationQuotient_finite_sections_and_support
      p q hp hp0 n hq hnot C hIC hprime P.1).1
  change (3 ∣ Module.finrank K (SchemeModuleOpenSectionsOver (nu ≫ pi)
    (SheafOfModules.unit N.ringCatSheaf) ⊤)) → 2 * pi.residueDegree P.1 ≤ Module.finrank K G
  intro hthree
  obtain ⟨Q, hQP, hQthree⟩ :=
    integralProper_genericNormalization_exists_closedPoint_above_with_three_degree X pi P hthree
  obtain ⟨U, hnonempty, hPU, ⟨eGlobal⟩⟩ :=
    selectedPrimeComponent_genericNormalizationQuotient_exists_globalSectionsEquiv_affineDefect
      p q hp hp0 n hq hnot C hIC hprime P.1
  letI : Nonempty U.1 := hnonempty
  let D := (ModuleCat.restrictScalars (schemeOpenBaseRingHom pi U.1)).obj
    (ModuleCat.of Γ(X, U.1) (localNormalizationDefect Γ(X, U.1) X.functionField))
  have eGlobalNative : G ≃ₗ[K] D := eGlobal
  have hfinite : Module.Finite K D := Module.Finite.equiv eGlobalNative
  have hQU : nu Q.1 ∈ U.1 := hQP.symm ▸ hPU
  have hclosed : IsClosed ({nu Q.1} : Set X) := hQP.symm ▸ P.2
  have hcopQ : Nat.Coprime (pi.residueDegree (nu Q.1)) 3 := hQP.symm ▸ hcop
  have hbound : 2 * pi.residueDegree (nu Q.1) ≤ Module.finrank K D :=
    genericNormalization_originalAffineDefect_ge_twice_residueDegree
      X pi U.1 U.2 hfinite Q hQU hclosed hcopQ hQthree
  rw [hQP] at hbound
  exact hbound.trans_eq eGlobalNative.finrank_eq.symm

/-- A singular actual point contributes its full original-K degree to the
OWN component defect. Native dimension and all affine/global data are derived. -/
theorem selectedPrimeComponent_nonregular_originalClosedPoint_degree_le_globalDefect
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal)
    (hprime : C.toIdeal.IsPrime) (P : closedPoints (scheme C))
    (hsing : ¬ IsRegularLocalRing ((scheme C).presheaf.stalk P.1)) :
    letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hprime P.1
    (toBase C).residueDegree P.1 ≤
      Module.finrank K (SchemeModuleGlobalSectionsOver (toBase C)
        (genericNormalizationQuotientSheaf (scheme C))) := by
  letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hprime P.1
  let X := scheme C
  let pi := toBase C
  let Q := genericNormalizationQuotientSheaf X
  obtain ⟨U, hnonempty, hxU, ⟨E⟩⟩ :=
    selectedPrimeComponent_genericNormalizationQuotient_exists_globalSectionsEquiv_affineDefect
      p q hp hp0 n hq hnot C hIC hprime P.1
  letI : Nonempty U.1 := hnonempty
  letI : Module.Finite K (SchemeModuleGlobalSectionsOver pi Q) :=
    (selectedProjectivePrimeComponent_genericNormalizationQuotient_finite_sections_and_support
      p q hp hp0 n hq hnot C hIC hprime P.1).1
  let D := (ModuleCat.restrictScalars (schemeOpenBaseRingHom pi U.1)).obj
    (ModuleCat.of Γ(X, U.1) (localNormalizationDefect Γ(X, U.1) X.functionField))
  have hfinite : Module.Finite K D := Module.Finite.equiv E
  have hdim := selectedProjectiveComponent_original_stalk_ringKrullDim_le_one
    p q hp hp0 n hq hnot C hIC P.1
  have hlocal := genericNormalization_originalClosedPoint_nonregular_degree_le_affineDefect
    X pi U.1 U.2 P hxU hdim hsing hfinite
  exact hlocal.trans E.finrank_eq.symm.le

/-- The SAME minimal component's full normalization constants rank divides
its OWN intrinsic degree mu. The actual OWN normalization cycle is internal. -/
theorem selectedMinimalComponent_genericNormalization_constantsRank_dvd_ownDegree
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (P : closedPoints (scheme C)) :
    letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hmin.isPrime P.1
    let X := scheme C
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    Module.finrank K (SchemeModuleOpenSectionsOver (nu ≫ toBase C)
      (SheafOfModules.unit N.ringCatSheaf) ⊤) ∣ actualCurveCoordinateHilbertDegree C := by
  letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hmin.isPrime P.1
  let X := scheme C
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : IsFinite nu := integralScheme_genericNormalization_isFinite X (toBase C)
  letI : IsProper (nu ≫ toBase C) := inferInstance
  obtain ⟨z, hz, _hbound⟩ := selectedMinimalComponent_genericNormalization_exists_own_degree_cycle
    p q hp hp0 n hq hnot C hmin
  have hdiv := integralProper_globalUnitSections_finrank_dvd_effectiveCycle_degree (nu ≫ toBase C) z
  exact hz ▸ hdiv

/-- OWN component Euler keeps both full constants ranks. Intrinsic H1<=G_n
and actual H0(C)>=1 yield the corrected OWN normalization defect upper bound. -/
theorem selectedPrimeComponent_genericNormalization_fullConstants_defect_bound
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal)
    (hprime : C.toIdeal.IsPrime) (P : closedPoints (scheme C)) :
    letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hprime P.1
    let X := scheme C
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    Module.finrank K (SchemeModuleGlobalSectionsOver (toBase C)
        (genericNormalizationQuotientSheaf X)) + 1 ≤
      Module.finrank K (SchemeModuleOpenSectionsOver (nu ≫ toBase C)
        (SheafOfModules.unit N.ringCatSheaf) ⊤) + (1 + 3 * n * (n - 1) / 2) := by
  letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hprime P.1
  let X := scheme C
  let pi := toBase C
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let ON : N.Modules := SheafOfModules.unit N.ringCatSheaf
  let Q := genericNormalizationQuotientSheaf X
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  letI : Linear K N.Modules := schemeModulesLinearOver (nu ≫ pi)
  have hEuler :
      (Module.finrank K (SchemeModuleOpenSectionsOver (nu ≫ pi) ON ⊤) : ℤ) -
        (Module.finrank K (schemeModuleCohomology N ON 1) : ℤ) =
      (Module.finrank K (SchemeModuleOpenSectionsOver pi OX ⊤) : ℤ) -
        (Module.finrank K (schemeModuleCohomology X OX 1) : ℤ) +
        (Module.finrank K (SchemeModuleGlobalSectionsOver pi Q) : ℤ) :=
    perfectField_selectedProjectivePrimeComponent_genericNormalization_unit_baseEuler_eq_curveEuler_add_fullQuotient
      p q hp hp0 n hq hnot C hIC hprime P.1
  have hH1 : Module.finrank K (schemeModuleCohomology X OX 1) ≤ 1 + 3 * n * (n - 1) / 2 :=
    (projectiveIntersection_closedComponent_unit_cohomology_one_finite_finrank_le
      p q hp hp0 n hn hq hnot C hIC).2
  obtain ⟨hfield, hfinite⟩ := integralProper_originalGlobalFunctions_field_and_unitSectionsFinite pi
  letI : Module.Finite K (SchemeModuleOpenSectionsOver pi OX ⊤) := hfinite
  letI : Field Γ(X, ⊤) := hfield.toField
  letI : Algebra K Γ(X, ⊤) := (schemeOpenBaseRingHom pi ⊤).toAlgebra
  let E := schemeModuleUnitTopOriginalRingLinearEquiv pi
  letI : Nontrivial (SchemeModuleOpenSectionsOver pi OX ⊤) :=
    E.toEquiv.nontrivial_congr.mpr inferInstance
  have hH0 : 1 ≤ Module.finrank K (SchemeModuleOpenSectionsOver pi OX ⊤) :=
    Module.finrank_pos
  change Module.finrank K (SchemeModuleGlobalSectionsOver pi Q) + 1 ≤
    Module.finrank K (SchemeModuleOpenSectionsOver (nu ≫ pi) ON ⊤) + (1 + 3 * n * (n - 1) / 2)
  omega

/-- An actual SAME minimal component through the original point is regular
at that point in A(ii), even when the whole selected curve is reducible or
nonreduced. OWN degree positivity/bound/divisibility and all defects are derived. -/
theorem coray_case_Aii_selectedMinimalComponent_originalClosedPoint_isRegularLocalRing
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 2 ≤ n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (hmuThree : 3 ∣ actualCurveCoordinateHilbertDegree C)
    (P : closedPoints (scheme C)) (hcop : Nat.Coprime ((toBase C).residueDegree P.1) 3)
    (hdegree : (toBase C).residueDegree P.1 ≤ 3 * (n + 1).choose 2)
    (hfreedom : 3 * (n + 1).choose 2 - (toBase C).residueDegree P.1 < 3) :
    IsRegularLocalRing ((scheme C).presheaf.stalk P.1) := by
  classical
  letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hmin.isPrime P.1
  let X := scheme C
  let pi := toBase C
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let a := Module.finrank K (SchemeModuleOpenSectionsOver (nu ≫ pi)
    (SheafOfModules.unit N.ringCatSheaf) ⊤)
  let delta := Module.finrank K (SchemeModuleGlobalSectionsOver pi (genericNormalizationQuotientSheaf X))
  have hbound : delta + 1 ≤ a + (3 * n.choose 2 + 1) := by
    rw [coray_choose_genus_eq_euler_bound n]
    exact selectedPrimeComponent_genericNormalization_fullConstants_defect_bound
      p q hp hp0 n (by omega) hq hnot C hmin.le hmin.isPrime P
  have hdiv : a ∣ actualCurveCoordinateHilbertDegree C :=
    selectedMinimalComponent_genericNormalization_constantsRank_dvd_ownDegree
      p q hp hp0 n hq hnot C hmin P
  have hmu := selectedProjectiveMinimalComponent_hilbertDegree_pos_bound_and_eventualIncrement_anyField
    p q hp hp0 n hq hnot C hmin
  have ha : a ≤ 3 * n := (Nat.le_of_dvd hmu.1 hdiv).trans hmu.2.1
  by_contra hsing
  by_cases hthree : 3 ∣ a
  · have hlower : 2 * pi.residueDegree P.1 ≤ delta :=
      selectedPrimeComponent_three_constants_globalDefect_ge_twice_point_degree
        p q hp hp0 n hq hnot C hmin.le hmin.isPrime P hcop hthree
    exact aii_twiceDegree_fullConstants_contradiction n a (pi.residueDegree P.1) delta
      hn ha hbound hlower hdegree hfreedom
  · obtain ⟨lambda, hlambda⟩ := hmuThree
    have hdivlambda : a ∣ lambda := by
      have hmul : a ∣ 3 * lambda := hlambda ▸ hdiv
      exact degree_delta_dvd_l_of_dvd_three_l a lambda hthree hmul
    have hpositive : 0 < lambda := by
      have h := hmu.1
      rw [hlambda] at h
      omega
    have hlambdabound : lambda ≤ n := by
      have h := hmu.2.1
      rw [hlambda] at h
      omega
    have han : a ≤ n := (Nat.le_of_dvd hpositive hdivlambda).trans hlambdabound
    have hlower : pi.residueDegree P.1 ≤ delta :=
      selectedPrimeComponent_nonregular_originalClosedPoint_degree_le_globalDefect
        p q hp hp0 n hq hnot C hmin.le hmin.isPrime P hsing
    have hstep : 3 * (n + 1).choose 2 = 3 * n.choose 2 + 3 * n := by
      simpa only [Nat.reduceAdd, Nat.choose_one_right, Nat.mul_add, Nat.add_comm] using
        congrArg (fun t : ℕ => 3 * t) (Nat.choose_succ_succ' n 1)
    dsimp only [a, delta, pi, nu, N, X] at han hlower hbound
    omega

/-- Actual least-original-degree A(ii) component endpoint: the own-degree
multiple-of-three branch is derived from its genuine smaller-point producer,
so no degree-divisibility, regularity, defect or GI premise remains. -/
theorem coray_case_Aii_selectedMinimalComponent_leastOriginalDegree_point_isRegularLocalRing
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 2 ≤ n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (P : closedPoints (scheme C)) (hcop : Nat.Coprime ((toBase C).residueDegree P.1) 3)
    (hleast : ∀ R : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 →
        (toBase C).residueDegree P.1 ≤ (hypersurfaceToBase p hp).residueDegree R.1)
    (hdegree : (toBase C).residueDegree P.1 ≤ 3 * (n + 1).choose 2)
    (hfreedom : 3 * (n + 1).choose 2 - (toBase C).residueDegree P.1 < 3) :
    IsRegularLocalRing ((scheme C).presheaf.stalk P.1) := by
  have hstep : 3 * (n + 1).choose 2 = 3 * n.choose 2 + 3 * n := by
    simpa only [Nat.reduceAdd, Nat.choose_one_right, Nat.mul_add, Nat.add_comm] using
      congrArg (fun t : ℕ => 3 * t) (Nat.choose_succ_succ' n 1)
  have hchoose : 1 ≤ n.choose 2 := Nat.choose_pos hn
  have hstrict : 3 * n < (toBase C).residueDegree P.1 := by omega
  have hmuThree : 3 ∣ actualCurveCoordinateHilbertDegree C := by
    by_contra h
    have hmuCop : Nat.Coprime (actualCurveCoordinateHilbertDegree C) 3 :=
      (Nat.prime_three.coprime_iff_not_dvd.mpr h).symm
    obtain ⟨R, hRcop, hRbound, hCbound⟩ :=
      selectedMinimalComponent_primeDegree_exists_originalCubic_point_bound
        p q hp hp0 n hq hnot C hmin hmuCop
    exact (not_lt_of_ge (hleast R hRcop)) (hRbound.trans_lt (hCbound.trans_lt hstrict))
  exact coray_case_Aii_selectedMinimalComponent_originalClosedPoint_isRegularLocalRing
    p q hp hp0 n hn hq hnot C hmin hmuThree P hcop hdegree hfreedom

/-- The actual through-P minimal component is selected internally and is
regular at its SAME degree-preserving original-point preimage in A(ii).
The whole p/q curve may be reducible or nonreduced; no component, own degree,
integrality, regularity, normalization lift or defect is an original input. -/
theorem coray_case_Aii_leastOriginalDegree_intersectionPoint_exists_regular_minimalComponent
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 2 ≤ n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (P : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)))
    (hcop : Nat.Coprime ((toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1) 3)
    (hleast : ∀ R : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 →
        (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1 ≤
          (hypersurfaceToBase p hp).residueDegree R.1)
    (hdegree : (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1 ≤
      3 * (n + 1).choose 2)
    (hfreedom : 3 * (n + 1).choose 2 -
      (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1 < 3) :
    ∃ (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
      (hIC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal),
      C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes ∧
      ∃ Q : closedPoints (scheme C),
        schemeQuotientMap (projectiveIntersectionIdeal p q hp hq) C hIC Q.1 = P.1 ∧
        IsIso ((schemeQuotientMap (projectiveIntersectionIdeal p q hp hq) C hIC).residueFieldMap Q.1) ∧
        (toBase C).residueDegree Q.1 =
          (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1 ∧
        IsRegularLocalRing ((scheme C).presheaf.stalk Q.1) := by
  obtain ⟨C, hIC, hmin, _hprime, Q, hmap, hiso, hQdegree⟩ :=
    homogeneousProjective_originalClosedPoint_exists_minimalComponent
      (projectiveIntersectionIdeal p q hp hq) P
  have hQcop : Nat.Coprime ((toBase C).residueDegree Q.1) 3 := hQdegree.symm ▸ hcop
  have hQleast : ∀ R : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 →
        (toBase C).residueDegree Q.1 ≤ (hypersurfaceToBase p hp).residueDegree R.1 :=
    hQdegree.symm ▸ hleast
  have hQupper : (toBase C).residueDegree Q.1 ≤ 3 * (n + 1).choose 2 := hQdegree.symm ▸ hdegree
  have hQfreedom : 3 * (n + 1).choose 2 - (toBase C).residueDegree Q.1 < 3 :=
    hQdegree.symm ▸ hfreedom
  exact ⟨C, hIC, hmin, Q, hmap, hiso, hQdegree,
    coray_case_Aii_selectedMinimalComponent_leastOriginalDegree_point_isRegularLocalRing
      p q hp hp0 n hn hq hnot C hmin Q hQcop hQleast hQupper hQfreedom⟩

end PfaffianDescent.Coray
