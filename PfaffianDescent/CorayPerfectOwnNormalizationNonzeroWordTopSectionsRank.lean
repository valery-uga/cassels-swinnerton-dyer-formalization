import PfaffianDescent.CorayPerfectOwnNormalizationNonzeroWordCokernel
import PfaffianDescent.CorayPerfectOwnNormalizationConstantsTower
import PfaffianDescent.FiniteFiveTermLinearRank

/-! SOURCE ONLY / UNVERIFIED. Actual original-K finite H0 and exact
connecting-IMAGE rank balance for the SAME GIVEN nonzero signed-word section
on the OWN normalization. Actual full constants are retained. No H1 finite,
Euler/genus or target signed-weight equality is assumed or claimed. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics.HomogeneousProjective IdealSheafDataModule
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Only actual H0 outer finiteness is needed. The actual connecting
IMAGE is finite as an image of finite quotient H0; H1 itself may be infinite. -/
private theorem nativeShortExact_topSections_finite_and_connectingImage_rank
    {K : Type u} [Field K] {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (CommRingCat.of K)) (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) →
    Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₃ ⊤) →
      Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₂ ⊤) ∧
      Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₂ ⊤) +
          Module.finrank K (schemeModuleOpenTopConnectingLinearMapOver pi S hS).range =
        Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) +
          Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₃ ⊤) ∧
      Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) ≤
        Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₂ ⊤) ∧
      Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₂ ⊤) ≤
        Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) +
          Module.finrank K (SchemeModuleOpenSectionsOver pi S.X₃ ⊤) := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  intro hfirst hthird
  letI : Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) := hfirst
  letI : Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₃ ⊤) := hthird
  letI : Mono S.f := hS.mono_f
  let f := schemeModuleOpenTopCoefficientLinearMapOver pi S.f
  let g := schemeModuleOpenTopCoefficientLinearMapOver pi S.g
  let delta := schemeModuleOpenTopConnectingLinearMapOver pi S hS
  have hfg : Function.Exact f g := schemeModuleOpenTopCoefficientLinearMaps_exact pi S hS
  have hgd : Function.Exact g delta := (schemeModuleOpenTopConnectingLinearMaps_exact pi S hS).1
  have hf : Function.Injective f := schemeModuleOpenTopCoefficientLinearMapOver_injective_of_mono pi S.f
  letI : Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₂ ⊤) := moduleFinite_middle_of_exact f g hfg
  have hgRank := g.finrank_range_add_finrank_ker
  rw [hfg.linearMap_ker_eq, LinearMap.finrank_range_of_inj hf] at hgRank
  have hdRank := delta.finrank_range_add_finrank_ker
  rw [hgd.linearMap_ker_eq] at hdRank
  dsimp only [delta] at hdRank
  exact ⟨inferInstance, by omega, by omega, by omega⟩

/-- SAME own finite constants H0 only; no word, HasExt or connecting map. -/
private theorem ownNormalization_unitTopSections_finite
    {K : Type u} [Field K] [PerfectField K]
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hprime : C.toIdeal.IsPrime) (P : scheme C) :
    letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hprime P
    let X := scheme C
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let pi := nu ≫ toBase C
    let O : N.Modules := SheafOfModules.unit N.ringCatSheaf
    Module.Finite K (SchemeModuleOpenSectionsOver pi O ⊤) := by
  exact (perfectField_homogeneousPrime_genericNormalization_originalConstants_finite_and_finrank_dvd
    C hprime P).2.2.1

/-- SAME actual quotient H0 only; no HasExt or connecting-map carrier. -/
private theorem ownNonzeroWord_cokernelTopSections_finite
    {K : Type u} [Field K] [PerfectField K]
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
    let O : N.Modules := SheafOfModules.unit N.ringCatSheaf
    ∀ ops : List (closedPoints N × Bool),
      let W : N.Modules := schemeModuleIteratedSignedClosedPointTensor O ops
      ∀ (s : W.val.obj (op ⊤)), s ≠ 0 →
        let Q : N.Modules := cokernel (schemeModuleTopSectionHom W s)
        Module.Finite K (SchemeModuleOpenSectionsOver pi Q ⊤) := by
  letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hmin.isPrime P
  let X := scheme C
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let pi := nu ≫ toBase C
  let O : N.Modules := SheafOfModules.unit N.ringCatSheaf
  change ∀ ops : List (closedPoints N × Bool),
    let W : N.Modules := schemeModuleIteratedSignedClosedPointTensor O ops
    ∀ (s : W.val.obj (op ⊤)), s ≠ 0 → _
  intro ops
  let W : N.Modules := schemeModuleIteratedSignedClosedPointTensor O ops
  change ∀ (s : W.val.obj (op ⊤)), s ≠ 0 → _
  intro s hs
  obtain ⟨_hfiniteSupport, _hpoints, _hlength, hQ, _hdegree⟩ :=
    perfectField_selectedProjectiveMinimalComponent_normalization_nonzeroWordSection_cokernel_finiteHZero_and_lengthCycle
      p q hp hp0 n hq hnot C hmin P ops s hs
  exact hQ

/-- Actual finite word H0 via SAME two coefficient maps; no connecting
image rank or H1 finiteness occurs in this declaration. -/
private theorem ownNonzeroWord_topSections_finite
    {K : Type u} [Field K] [PerfectField K]
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
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    let O : N.Modules := SheafOfModules.unit N.ringCatSheaf
    ∀ ops : List (closedPoints N × Bool),
      let W : N.Modules := schemeModuleIteratedSignedClosedPointTensor O ops
      ∀ (s : W.val.obj (op ⊤)), s ≠ 0 →
        Module.Finite K (SchemeModuleOpenSectionsOver pi W ⊤) := by
  letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hmin.isPrime P
  let X := scheme C
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let pi := nu ≫ toBase C
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K N.Modules := schemeModulesLinearOver pi
  let O : N.Modules := SheafOfModules.unit N.ringCatSheaf
  change ∀ ops : List (closedPoints N × Bool),
    let W : N.Modules := schemeModuleIteratedSignedClosedPointTensor O ops
    ∀ (s : W.val.obj (op ⊤)), s ≠ 0 → _
  intro ops
  let W : N.Modules := schemeModuleIteratedSignedClosedPointTensor O ops
  change ∀ (s : W.val.obj (op ⊤)), s ≠ 0 → _
  intro s hs
  let Q : N.Modules := cokernel (schemeModuleTopSectionHom W s)
  let S : ShortComplex N.Modules := ShortComplex.cokernelSequence (schemeModuleTopSectionHom W s)
  have hS : S.ShortExact :=
    (perfectField_selectedProjectiveMinimalComponent_normalization_nonzeroWordSection_mono_and_genericZero
      p q hp hp0 n hq hnot C hmin P ops s hs).2.2.1
  letI : Module.Finite K (SchemeModuleOpenSectionsOver pi O ⊤) :=
    ownNormalization_unitTopSections_finite C hmin.isPrime P
  letI : Module.Finite K (SchemeModuleOpenSectionsOver pi Q ⊤) :=
    ownNonzeroWord_cokernelTopSections_finite p q hp hp0 n hq hnot C hmin P ops s hs
  letI : Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₁ ⊤) := by
    change Module.Finite K (SchemeModuleOpenSectionsOver pi O ⊤)
    exact ownNormalization_unitTopSections_finite C hmin.isPrime P
  letI : Module.Finite K (SchemeModuleOpenSectionsOver pi S.X₃ ⊤) := by
    change Module.Finite K (SchemeModuleOpenSectionsOver pi Q ⊤)
    exact ownNonzeroWord_cokernelTopSections_finite p q hp hp0 n hq hnot C hmin P ops s hs
  exact moduleFinite_middle_of_exact
    (schemeModuleOpenTopCoefficientLinearMapOver pi S.f)
    (schemeModuleOpenTopCoefficientLinearMapOver pi S.g)
    (schemeModuleOpenTopCoefficientLinearMaps_exact pi S hS)

/-- Actual exact connecting-IMAGE rank balance. SAME full constants and
actual quotient/word H0 are separately constructed, without wholeH1 finiteness. -/
theorem perfectField_selectedProjectiveMinimalComponent_normalization_nonzeroWordSection_topSections_finite_and_connectingImage_rank
    {K : Type u} [Field K] [PerfectField K]
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
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    letI : Linear K N.Modules := schemeModulesLinearOver pi
    let O : N.Modules := SheafOfModules.unit N.ringCatSheaf
    ∀ ops : List (closedPoints N × Bool),
      let W : N.Modules := schemeModuleIteratedSignedClosedPointTensor O ops
      ∀ (s : W.val.obj (op ⊤)), s ≠ 0 →
        let Q : N.Modules := cokernel (schemeModuleTopSectionHom W s)
        let S : ShortComplex N.Modules := ShortComplex.cokernelSequence (schemeModuleTopSectionHom W s)
        ∃ hS : S.ShortExact,
          Module.Finite K (SchemeModuleOpenSectionsOver pi W ⊤) ∧
          Module.finrank K (SchemeModuleOpenSectionsOver pi W ⊤) +
              Module.finrank K (schemeModuleOpenTopConnectingLinearMapOver pi S hS).range =
            Module.finrank K (SchemeModuleOpenSectionsOver pi O ⊤) +
              Module.finrank K (SchemeModuleOpenSectionsOver pi Q ⊤) ∧
          Module.finrank K (SchemeModuleOpenSectionsOver pi O ⊤) ≤
            Module.finrank K (SchemeModuleOpenSectionsOver pi W ⊤) ∧
          Module.finrank K (SchemeModuleOpenSectionsOver pi W ⊤) ≤
            Module.finrank K (SchemeModuleOpenSectionsOver pi O ⊤) +
              Module.finrank K (SchemeModuleOpenSectionsOver pi Q ⊤) := by
  letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hmin.isPrime P
  let X := scheme C
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let pi := nu ≫ toBase C
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K N.Modules := schemeModulesLinearOver pi
  let O : N.Modules := SheafOfModules.unit N.ringCatSheaf
  change ∀ ops : List (closedPoints N × Bool),
    let W : N.Modules := schemeModuleIteratedSignedClosedPointTensor O ops
    ∀ (s : W.val.obj (op ⊤)), s ≠ 0 → _
  intro ops
  let W : N.Modules := schemeModuleIteratedSignedClosedPointTensor O ops
  change ∀ (s : W.val.obj (op ⊤)), s ≠ 0 → _
  intro s hs
  let Q : N.Modules := cokernel (schemeModuleTopSectionHom W s)
  let S : ShortComplex N.Modules := ShortComplex.cokernelSequence (schemeModuleTopSectionHom W s)
  have hS : S.ShortExact :=
    (perfectField_selectedProjectiveMinimalComponent_normalization_nonzeroWordSection_mono_and_genericZero
      p q hp hp0 n hq hnot C hmin P ops s hs).2.2.1
  letI : Module.Finite K (SchemeModuleOpenSectionsOver pi O ⊤) :=
    ownNormalization_unitTopSections_finite C hmin.isPrime P
  letI : Module.Finite K (SchemeModuleOpenSectionsOver pi Q ⊤) :=
    ownNonzeroWord_cokernelTopSections_finite p q hp hp0 n hq hnot C hmin P ops s hs
  have hW : Module.Finite K (SchemeModuleOpenSectionsOver pi W ⊤) :=
    ownNonzeroWord_topSections_finite p q hp hp0 n hq hnot C hmin P ops s hs
  have hRank := nativeShortExact_topSections_finite_and_connectingImage_rank pi S hS
    (show Module.Finite K (SchemeModuleOpenSectionsOver pi O ⊤) from inferInstance)
    (show Module.Finite K (SchemeModuleOpenSectionsOver pi Q ⊤) from inferInstance)
  exact ⟨hS, hW, hRank.2⟩

end PfaffianDescent.Coray
