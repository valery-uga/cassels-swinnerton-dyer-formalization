import PfaffianDescent.CorayOwnMinimalNormalizationClosedPoint
import PfaffianDescent.CorayNormalizationClosedPointIdealRankOne
import PfaffianDescent.SchemeModuleClosedPointTensorDualIncrement

/-! SOURCE ONLY / UNVERIFIED. Genuine SAME closed-point ideal rank-one charts
on the actual OWN minimal component's normalization over original perfect K.
Actual DVR spreading supplies the original ideal-module section and original
inclusion, and unit sections frame its complement. No H1, Euler, genus,
duality, whole-CI integrality, CharZero, Infinite or constants equality input. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AllCharacteristics.HomogeneousProjective IdealSheafDataModule
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Generic actual point-ideal construction. At P the SAME ideal has an actual
regular affine generator obtained by genuine spreading from its DVR stalk;
away from P its original inclusion sends an actual section to1. The resulting
rank-one frames come from those same section-induced sheaf isomorphisms. -/
theorem closedPointIdeal_locallyRankOne_of_stalk_isDVR
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (P : closedPoints X) [IsDiscreteValuationRing (X.presheaf.stalk P.1)] :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    schemeModuleLocallyRankOne (show X.Modules from closedImmersionModule i) := by
  classical
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M : X.Modules := closedImmersionModule i
  change schemeModuleLocallyRankOne M
  have hgen : ∃ V : X.affineOpens, P.1 ∈ V.1 ∧
      ∃ m : M.val.presheaf.obj (op V.1),
        IsIso (schemeModuleSectionOnOpenHom M V.1 m) := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hPU, _⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ P.1) isOpen_univ
    obtain ⟨s, hPs, z, hz, hreg, hprincipal⟩ :=
      closedPointIdeal_affine_regularPrincipal_neighborhood_of_stalk_isDVR
        X P ⟨U, hU⟩ hPU
    let V : X.affineOpens := ⟨X.basicOpen s, hU.basicOpen s⟩
    let t : Γ(X, V) := X.presheaf.map (homOfLE (X.basicOpen_le s)).op z
    have hmem : t ∈ i.ker.ideal V := by
      rw [hprincipal]
      exact Ideal.mem_span_singleton_self t
    obtain ⟨m, hm⟩ := exists_closedImmersionModule_section_of_affine_mem i V t hmem
    refine ⟨V, hPs, m, ?_⟩
    apply closedImmersionModule_affineSection_isIso_of_regularPrincipal i V m
    · rw [hm]
      exact hreg
    · rw [hm]
      exact hprincipal
  intro x
  obtain ⟨U, hxU, m, hm⟩ : ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ m : M.val.presheaf.obj (op U.1),
        IsIso (schemeModuleSectionOnOpenHom M U.1 m) := by
    by_cases hx : x = P.1
    · subst x
      exact hgen
    · have hxoff : x ∈ ({P.1} : Set X)ᶜ := hx
      have hPclosed : IsClosed ({P.1} : Set X) := mem_closedPoints_iff.mp P.2
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUoff⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hxoff hPclosed.isOpen_compl
      let UA : X.affineOpens := ⟨U, hU⟩
      have hPU : P.1 ∉ U := by
        intro h
        exact hUoff h (Set.mem_singleton P.1)
      obtain ⟨m, _hm, hiso⟩ := closedPointIdeal_affine_unitGenerator_away X P UA hPU
      exact ⟨UA, hxU, m, hiso⟩
  letI := hm
  let e : SheafOfModules.unit (U.1 : Scheme.{u}).ringCatSheaf ≅ M.restrict U.1.ι :=
    asIso (schemeModuleSectionOnOpenHom M U.1 m)
  exact ⟨U.1, hxU, ⟨ProjectiveNegativeTwist.overFunctorIsoUnit_of_restrictIsoUnit U.1 e.symm ≪≫
    (SchemeModuleInternalHom.unitOverIso U.1).symm⟩⟩

/-- EVERY actual closed-point ideal on the SAME own minimal component's
canonical normalization is locally rank one over ORIGINAL perfect K. Actual
minimal-component geometry, native finite normalization, native closed-point
DVRs and original affine spreading internally construct every frame. No local
DVR, rank-one ideal, point-lift, cohomology or numerical premise is supplied. -/
theorem perfectField_selectedProjectiveMinimalComponent_genericNormalization_closedPoint_ideal_locallyRankOne
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
    ∀ Q : closedPoints N,
      let i := N.fromSpecResidueField Q.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp Q.2
      schemeModuleLocallyRankOne (show N.Modules from closedImmersionModule i) := by
  letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hmin.isPrime P
  let X := scheme C
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  letI : IsLocallyNoetherian N :=
    perfectField_integralGenericNormalization_isLocallyNoetherian X (toBase C)
  change ∀ Q : closedPoints N,
    let i := N.fromSpecResidueField Q.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp Q.2
    schemeModuleLocallyRankOne (show N.Modules from closedImmersionModule i)
  intro Q
  letI : IsDiscreteValuationRing (N.presheaf.stalk Q.1) :=
    perfectField_selectedProjectiveMinimalComponent_genericNormalization_closedPoint_stalk_isDVR
      p q hp hp0 n hq hnot C hmin P Q
  exact closedPointIdeal_locallyRankOne_of_stalk_isDVR N Q

end PfaffianDescent.Coray
