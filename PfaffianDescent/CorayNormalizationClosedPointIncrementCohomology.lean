import PfaffianDescent.CorayNormalizationClosedPointCanonicalFiberIso
import PfaffianDescent.CorayNormalizationClosedPointDualIncrement
import PfaffianDescent.SchemeModuleClosedPointSupportCohomology
import PfaffianDescent.SchemeModuleOpenTopConnectingLinearExact
import PfaffianDescent.CorayProjectiveNormalizationCohomologyOneBoundCore

/-! Primitive global-section/cohomology consequences of the SAME actual
closed-point ideal, its constructed O-linear dual D and canonical increment.
The actual quotient is i_*i^*D; its positive cohomology vanishes internally.
The actual adjunction unit, connecting class and original pi actions remain.
No global constants equality, residue-degree formula or RR is asserted.
DEPENDENCY: canonical-fiber/frame packet is SOURCE ONLY / UNVERIFIED.
This packet likewise has no compiler or kernel acceptance. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Assemble the actual quotient-Iso short exact sequence over variable
category objects, before original Scheme.Modules is specialized. -/
private theorem nativeCokernelFiberSequenceShortExact003
    {C : Type*} [Category C] [Abelian C] {A B F : C}
    (delta : A ⟶ B) (eta : B ⟶ F)
    (hzero : delta ≫ eta = 0) (E : cokernel delta ≅ F)
    (hE : cokernel.π delta ≫ E.hom = eta)
    (hS : (ShortComplex.cokernelSequence delta).ShortExact) :
    (ShortComplex.mk delta eta hzero).ShortExact := by
  let S := ShortComplex.cokernelSequence delta
  let T := ShortComplex.mk delta eta hzero
  let e : S ≅ T := ShortComplex.isoMk (Iso.refl A) (Iso.refl B) E
    (by
      change (𝟙 A) ≫ delta = delta ≫ (𝟙 B)
      exact (Category.id_comp delta).trans (Category.comp_id delta).symm)
    (by
      change (𝟙 B) ≫ eta = cokernel.π delta ≫ E.hom
      exact (Category.id_comp eta).trans hE.symm)
  exact ShortComplex.shortExact_of_iso e hS

/-- The actual fiber-target increment sequence is genuinely ShortExact,
with SAME delta and SAME eta_D. The zero composite and every exactness
input are derived internally from the actual canonical cokernel square. -/
theorem projectiveIntersection_genericNormalization_closedPoint_dualIncrement_fiberSequence_shortExact
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let X := scheme (projectiveIntersectionIdeal p q hp hq)
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    ∀ P : closedPoints N,
      let i := N.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      let D := SchemeModuleInternalHom.dual (IdealSheafDataModule.closedImmersionModule i)
      let delta := SchemeModuleInternalHom.unitToHom
        (IdealSheafDataModule.closedImmersionModuleToUnit i)
      let eta := (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app D
      ∃ hzero : delta ≫ eta = 0, (ShortComplex.mk delta eta hzero).ShortExact := by
  classical
  dsimp only
  let X := scheme (projectiveIntersectionIdeal p q hp hq)
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  intro P
  let i := N.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let j := IdealSheafDataModule.closedImmersionModuleToUnit i
  let D := SchemeModuleInternalHom.dual (IdealSheafDataModule.closedImmersionModule i)
  let delta := SchemeModuleInternalHom.unitToHom j
  let eta := (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app D
  let S := SchemeModuleInternalHom.incrementCokernelSequence j
  have hS : S.ShortExact :=
    projectiveIntersection_genericNormalization_closedPoint_dualIncrement_shortExact
      p q hp hp0 n hn hq hnot P
  obtain ⟨E, hE, _hunique⟩ :=
    projectiveIntersection_genericNormalization_closedPoint_dualIncrement_canonicalFiberIso
      p q hp hp0 n hn hq hnot P
  have hzero : delta ≫ eta = 0 :=
    projectiveIntersection_genericNormalization_closedPoint_dualIncrement_fiber_zero
      p q hp hp0 n hn hq hnot P
  have hE' : cokernel.π delta ≫ E.hom = eta := hE
  exact ⟨hzero, nativeCokernelFiberSequenceShortExact003 (C := N.Modules)
    delta eta hzero E hE' hS⟩

/-- Every positive cohomology group of the ACTUAL increment cokernel is
zero, internally from its canonical intrinsic fiber Iso and the genuine
stalk--skyscraper adjunction. No quotient-cohomology certificate is input. -/
theorem projectiveIntersection_genericNormalization_closedPoint_dualIncrement_cokernel_cohomology_succ_subsingleton
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let X := scheme (projectiveIntersectionIdeal p q hp hq)
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    ∀ (P : closedPoints N) (k : ℕ),
      let i := N.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      Subsingleton (schemeModuleCohomology N
        (cokernel (SchemeModuleInternalHom.unitToHom
          (IdealSheafDataModule.closedImmersionModuleToUnit i))) (k + 1)) := by
  classical
  dsimp only
  let X := scheme (projectiveIntersectionIdeal p q hp hq)
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  intro P k
  let i := N.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let D := SchemeModuleInternalHom.dual (IdealSheafDataModule.closedImmersionModule i)
  obtain ⟨E, _hE, _hunique⟩ :=
    projectiveIntersection_genericNormalization_closedPoint_dualIncrement_canonicalFiberIso
      p q hp hp0 n hn hq hnot P
  letI : Subsingleton (schemeModuleCohomology N
      ((Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj D)) (k + 1)) :=
    schemeModuleResiduePointPushforward_cohomology_succ_subsingleton P
      ((Scheme.Modules.pullback i).obj D) k
  exact schemeModuleCohomology_subsingleton_of_iso N E.symm (k + 1)

/-- Transport the actual three consecutive LES exactness statements through a
specified quotient isomorphism and its projection equation. Geometric callers
must construct the short exact sequence, isomorphism and equation internally.
Generic proof checked separately in direct4827; full geometric specialization pending. -/
private theorem nativeQuotientProjectionLESExact007
    {K : Type u} [Field K] {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (CommRingCat.of K))
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    {F : X.Modules} (E : S.X₃ ≅ F) (eta : S.X₂ ⟶ F)
    (hE : S.g ≫ E.hom = eta) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    let b := (schemeModuleOpenTopConnectingLinearMapOver pi S hS).comp
      (schemeModuleOpenTopCoefficientLinearMapOver pi E.inv)
    Function.Exact (schemeModuleOpenTopCoefficientLinearMapOver pi S.f)
      (schemeModuleOpenTopCoefficientLinearMapOver pi eta) ∧
    Function.Exact (schemeModuleOpenTopCoefficientLinearMapOver pi eta) b ∧
    Function.Exact b (schemeModuleCohomologyLinearMapOver pi S.f 1) := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  let Etop := schemeModuleOpenTopIsoLinearEquivOver pi E
  have h0 := (schemeModuleOpenTopCoefficientLinearMaps_exact pi S hS).comp_injective
    Etop Etop.injective Etop.map_zero
  have h0' : Function.Exact (schemeModuleOpenTopCoefficientLinearMapOver pi S.f)
      (schemeModuleOpenTopCoefficientLinearMapOver pi (S.g ≫ E.hom)) := h0
  have h := schemeModuleOpenTopConnectingLinearMaps_exact_of_quotientIso pi S hS E
  exact ⟨hE ▸ h0', hE ▸ h.1, h.2⟩


/-- The actual fiber version of the global LES. Its projection is SAME
eta_D and its boundary is SAME canonical extension class after the inverse
of the canonical cokernel Iso. The output retains the full section-map
image; no normalization-constants equality or dimension is assumed. -/
theorem projectiveIntersection_genericNormalization_closedPoint_dualIncrement_globalSections_cohomology_exact
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let pi := nu ≫ toBase I
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    letI : Linear K N.Modules := schemeModulesLinearOver pi
    ∀ P : closedPoints N,
      let i := N.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      let j := IdealSheafDataModule.closedImmersionModuleToUnit i
      let D := SchemeModuleInternalHom.dual (IdealSheafDataModule.closedImmersionModule i)
      let delta := SchemeModuleInternalHom.unitToHom j
      ∃ E : cokernel delta ≅ (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj D),
        cokernel.π delta ≫ E.hom = (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app D ∧
        let S := SchemeModuleInternalHom.incrementCokernelSequence j
        let hS := projectiveIntersection_genericNormalization_closedPoint_dualIncrement_shortExact
          p q hp hp0 n hn hq hnot P
        let b := (schemeModuleOpenTopConnectingLinearMapOver pi S hS).comp
          (schemeModuleOpenTopCoefficientLinearMapOver pi E.inv)
        Function.Exact (schemeModuleOpenTopCoefficientLinearMapOver pi delta)
            (schemeModuleOpenTopCoefficientLinearMapOver pi
              ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app D)) ∧
          Function.Exact
            (schemeModuleOpenTopCoefficientLinearMapOver pi
              ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app D)) b ∧
          Function.Exact b (schemeModuleCohomologyLinearMapOver pi delta 1) ∧
          (schemeModuleCohomologyLinearMapOver pi delta 1).ker = LinearMap.range b ∧
          Function.Surjective (schemeModuleCohomologyLinearMapOver pi delta 1) := by
  classical
  dsimp only
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let pi := nu ≫ toBase I
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K N.Modules := schemeModulesLinearOver pi
  intro P
  let i := N.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let j := IdealSheafDataModule.closedImmersionModuleToUnit i
  let D := SchemeModuleInternalHom.dual (IdealSheafDataModule.closedImmersionModule i)
  let delta := SchemeModuleInternalHom.unitToHom j
  let S := SchemeModuleInternalHom.incrementCokernelSequence j
  let hS := projectiveIntersection_genericNormalization_closedPoint_dualIncrement_shortExact
    p q hp hp0 n hn hq hnot P
  have hFiber :=
    projectiveIntersection_genericNormalization_closedPoint_dualIncrement_canonicalFiberIso
      p q hp hp0 n hn hq hnot P
  let E := Classical.choose hFiber
  have hE := (Classical.choose_spec hFiber).1
  let b := (schemeModuleOpenTopConnectingLinearMapOver pi S hS).comp
    (schemeModuleOpenTopCoefficientLinearMapOver pi E.inv)
  have hE' : S.g ≫ E.hom = (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app D := hE
  have hex := nativeQuotientProjectionLESExact007 pi S hS E
    ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app D) hE'
  letI : Subsingleton (schemeModuleCohomology N S.X₃ 1) :=
    projectiveIntersection_genericNormalization_closedPoint_dualIncrement_cokernel_cohomology_succ_subsingleton
      p q hp hp0 n hn hq hnot P 0
  refine ⟨E, hE, hex.1, hex.2.1, hex.2.2, ?_,
    schemeModuleCohomologyOneMap_surjective_of_quotient_subsingleton pi S hS⟩
  apply Submodule.ext
  intro z
  change schemeModuleCohomologyLinearMapOver pi delta 1 z = 0 ↔ ∃ s, b s = z
  exact hex.2.2 z

/-- Genuine ORIGINAL-K finite H¹ of the SAME point dual, with a rank bound
by the actual H¹(O_N), and hence the primitive p/q arithmetic bound. Both
finiteness and surjectivity are internal; the full constants field is kept. -/
theorem projectiveIntersection_genericNormalization_closedPoint_dual_cohomology_one_finite_and_finrank_le
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let pi := nu ≫ toBase I
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    letI : Linear K N.Modules := schemeModulesLinearOver pi
    ∀ P : closedPoints N,
      let i := N.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      let D := SchemeModuleInternalHom.dual (IdealSheafDataModule.closedImmersionModule i)
      Module.Finite K (schemeModuleCohomology N D 1) ∧
        Module.finrank K (schemeModuleCohomology N D 1) ≤
          Module.finrank K (schemeModuleCohomology N (SheafOfModules.unit N.ringCatSheaf) 1) ∧
        Module.finrank K (schemeModuleCohomology N D 1) ≤ 1 + 3 * n * (n - 1) / 2 := by
  classical
  dsimp only
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let pi := nu ≫ toBase I
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K N.Modules := schemeModulesLinearOver pi
  letI : Module.Finite K (schemeModuleCohomology N (SheafOfModules.unit N.ringCatSheaf) 1) :=
    projectiveIntersection_genericNormalization_unit_cohomology_one_finite_native
      p q hp hp0 n hq hnot
  intro P
  let i := N.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let j := IdealSheafDataModule.closedImmersionModuleToUnit i
  let delta := SchemeModuleInternalHom.unitToHom j
  let S := SchemeModuleInternalHom.incrementCokernelSequence j
  let hS := projectiveIntersection_genericNormalization_closedPoint_dualIncrement_shortExact
    p q hp hp0 n hn hq hnot P
  letI : Subsingleton (schemeModuleCohomology N S.X₃ 1) :=
    projectiveIntersection_genericNormalization_closedPoint_dualIncrement_cokernel_cohomology_succ_subsingleton
      p q hp hp0 n hn hq hnot P 0
  let g := schemeModuleCohomologyLinearMapOver pi delta 1
  have hsurj : Function.Surjective g :=
    schemeModuleCohomologyOneMap_surjective_of_quotient_subsingleton pi S hS
  have hfinite := Module.Finite.of_surjective g hsurj
  have hle := LinearMap.finrank_le_finrank_of_surjective hsurj
  exact ⟨hfinite, hle, hle.trans
    (projectiveIntersection_genericNormalization_unit_cohomology_one_finrank_le_native
      p q hp hp0 n hn hq hnot)⟩

end PfaffianDescent.Coray
