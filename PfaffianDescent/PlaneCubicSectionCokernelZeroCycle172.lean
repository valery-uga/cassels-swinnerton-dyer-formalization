import PfaffianDescent.ProjectiveCurveSectionCokernel172
import PfaffianDescent.CorayPlaneCubicChartRegularCurve
import PfaffianDescent.CorayNonzeroIdealRegularCurve
import PfaffianDescent.CorayProjectiveNormalizationStalkDimension
import PfaffianDescent.CorayNormalizationNonzeroSignedWordStalkQuotient
import PfaffianDescent.SchemeModuleFiniteClosedSupportLengthCycle
import AllCharacteristics.SmoothSchemeRegularity

/-! SOURCE ONLY172. Native zero-divisor cycle of an arbitrary nonzero
section on the SAME smooth integral Fin3 cubic. The actual section cokernel
retains every stalk length and original residue-field factor. The signed-word
module is imported solely for its generic native-frame lemma. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Dimension of every actual stalk, through the original coordinate
chart and its prime localization. No smoothness or dimension premise. -/
theorem planeCubic_original_stalk_ringKrullDim_le_one172
    (p : MvPolynomial (Fin 3) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (x : scheme (equationIdeal p hp)) :
    ringKrullDim ((scheme (equationIdeal p hp)).presheaf.stalk x) ≤ 1 := by
  let I := equationIdeal p hp
  obtain ⟨j, y, hy⟩ := exists_coordinate_chart I x
  rw [← hy, ringKrullDim_eq_of_ringEquiv
    (asIso ((chartι I j).stalkMap y)).commRingCatIsoToRingEquiv,
    ringKrullDim_eq_of_ringEquiv
      (Spec.stalkIso (.of (ChartRing I j)) y).commRingCatIsoToRingEquiv]
  exact planeCubic_chartLocal_ringKrullDim_le_one p hp hp0 j y.asIdeal

/-- The domain-sensitive dimension-one property uses the genuine
integrality of the original cubic. The preceding Krull dimension bound
remains valid for every nonzero homogeneous cubic. -/
theorem planeCubic_original_stalk_dimensionLEOne172
    (p : MvPolynomial (Fin 3) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsIntegral (scheme (equationIdeal p hp))]
    (x : scheme (equationIdeal p hp)) :
    Ring.DimensionLEOne ((scheme (equationIdeal p hp)).presheaf.stalk x) := by
  letI : Ring.KrullDimLE 1 ((scheme (equationIdeal p hp)).presheaf.stalk x) :=
    Ring.krullDimLE_iff.mpr (planeCubic_original_stalk_ringKrullDim_le_one172 p hp hp0 x)
  exact ⟨fun {_} hn hp => hp.isMaximal_of_ne_bot hn⟩

/-- Smoothness gives actual regular local rings. Nongenericity rules out
a field, so the derived principal maximal ideal gives the genuine DVR. -/
theorem planeCubic_original_nongeneric_stalk_isDVR172
    (p : MvPolynomial (Fin 3) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (scheme (equationIdeal p hp))]
    (x : scheme (equationIdeal p hp)) (hx : x ≠ genericPoint (scheme (equationIdeal p hp))) :
    IsDiscreteValuationRing ((scheme (equationIdeal p hp)).presheaf.stalk x) := by
  let X := scheme (equationIdeal p hp)
  let R := X.presheaf.stalk x
  letI : IsRegularRing Γ(Spec (.of K), ⊤) := IsRegularRing.of_ringEquiv
    (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm
  letI : IsRegularLocalRing R :=
    AllCharacteristics.isRegularLocalRing_stalk_of_smooth_over_affine
      (hypersurfaceToBase p hp) x
  letI : IsPrincipalIdealRing R := regularLocalDomain_isPrincipalIdealRing_of_dimension_le_one
    (planeCubic_original_stalk_ringKrullDim_le_one172 p hp hp0 x)
  have hnot : ¬ IsField R := integralScheme_nongeneric_stalk_not_isField X x hx
  have hdvr : (IsLocalRing.maximalIdeal R).IsPrincipal ↔ IsDiscreteValuationRing R :=
    (IsDiscreteValuationRing.TFAE R hnot).out 4 0 (by rfl) (by rfl)
  exact hdvr.mp inferInstance

/-- A GIVEN nonzero section of ANY locally rank-one coefficient produces
the finite actual zero-divisor cycle and its exact original-field rank.
Native support, finite stalk length, finite top sections and zero H1 are
all constructed. No genus, Euler formula, divisor degree or duality input. -/
theorem planeCubic_nonzeroRankOneSection_cokernel_zeroCycle_data172
    (p : MvPolynomial (Fin 3) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (scheme (equationIdeal p hp))]
    (M : (scheme (equationIdeal p hp)).Modules) (hM : schemeModuleLocallyRankOne M)
    (s : M.val.obj (op ⊤)) (hs : s ≠ 0) :
    let I := equationIdeal p hp
    let X := scheme I
    let pi := toBase I
    let Q := cokernel (schemeModuleTopSectionHom M s)
    let C := schemeModuleStalkSupport Q
    letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} X.Modules :=
      CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
    ∃ (hC : C.Finite) (hc : ∀ x ∈ C, IsClosed ({x} : Set X)),
      Module.Finite K (SchemeModuleOpenSectionsOver pi Q ⊤) ∧
      Subsingleton (schemeModuleCohomology X Q 1) ∧
      EffectiveZeroCycle.degree pi (schemeModuleFiniteClosedSupportLengthCycle Q C hC hc) =
        Module.finrank K (SchemeModuleOpenSectionsOver pi Q ⊤) := by
  classical
  let I := equationIdeal p hp
  let X := scheme I
  let pi := toBase I
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pi
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace pi
  letI : IsNoetherian X :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules :=
    CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  let φ := schemeModuleTopSectionHom M s
  let Q := (show X.Modules from cokernel φ)
  let C := schemeModuleStalkSupport Q
  have hdim (x : X) : Ring.DimensionLEOne (X.presheaf.stalk x) :=
    planeCubic_original_stalk_dimensionLEOne172 p hp hp0 x
  obtain ⟨U, hgU, ⟨eU⟩⟩ := hM (genericPoint X)
  letI : Mono φ :=
    (schemeModuleTopSectionHom_mono_and_cokernelSequence_shortExact pi M hM U hgU eU s hs).1
  obtain ⟨_hclosed, hC, hc⟩ :=
    integralCurve_nonzeroRankOneSection_cokernel_support_finite_closed X pi hdim M hM s hs
  have hlength (x : C) : IsFiniteLength (X.presheaf.stalk x.1)
      ((schemeModuleStalkModuleFunctor X x.1).obj Q) := by
    have hx : x.1 ≠ genericPoint X := by
      intro hx
      have hz := schemeModuleTopSectionHom_cokernel_genericStalk_isZero pi M hM U hgU eU s hs
      have hsub := ModuleCat.subsingleton_of_isZero hz
      have hn : Nontrivial ((Scheme.Modules.presheaf (X := X) Q).stalk (genericPoint X)) := by
        have hxmem := x.2
        change Nontrivial ((Scheme.Modules.presheaf (X := X) Q).stalk x.1) at hxmem
        simpa only [hx] using hxmem
      exact (not_nontrivial_iff_subsingleton.mpr hsub) hn
    letI : IsDiscreteValuationRing (X.presheaf.stalk x.1) :=
      planeCubic_original_nongeneric_stalk_isDVR172 p hp hp0 x.1 hx
    obtain ⟨eW⟩ := schemeModuleLocallyRankOne_nativeStalkFrame M hM x.1
    exact schemeModuleUnitHomStalkCokernel_isFiniteLength M φ x.1 eW
  have hfinite := (schemeModuleOriginalBaseTopSections_finite_and_weighted_finrank
    pi Q C hC hc Set.Subset.rfl hlength).1
  exact ⟨hC, hc, hfinite,
    projectiveIntegralCurve_nonzeroRankOneSection_cokernel_hOne_zero I hdim M hM s hs,
    schemeModuleFiniteClosedSupportLengthCycle_degree_eq_topSections_finrank
      pi Q C hC hc Set.Subset.rfl hlength⟩

end PfaffianDescent.Coray
