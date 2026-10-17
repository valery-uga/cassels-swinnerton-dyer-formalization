import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualOriginalChosenSeed
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualOriginalGoodSelectedIncidenceDatum
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualChosenSupportEmbedding

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AllCharacteristics
namespace PfaffianDescent.ProjectiveNegativeTwist
open BundleSectionZeroLocus AllCharacteristics.HomogeneousProjective SerreExtensionData
open PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_original_chosen_parameter_residual_eight
    (K : Type u) [Field K] {E L₃ : Type u} [Field E] [Field L₃] [Algebra K E] [Algebra K L₃] [FiniteDimensional K L₃]
    {B : Scheme.{u}}
    [HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules]
    [HasExt.{u} (SheafOfModules.{u}
      (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).ringCatSheaf)]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] {L : Type u} [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
    [hExt : HasExt.{u} (hypersurface p hp).Modules]
    [hExtStalk : HasExt.{u + 1}
      (ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (i default)))]
    (e : SerreExtensionData (hypersurface p hp)
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)))
    (hne :
      letI := quotientPositiveTwist_tensorRight_preservesFiniteLimits (equationIdeal p hp) 3
      letI := quotientPositiveTwist_tensorRight_preservesFiniteColimits (equationIdeal p hp) 3
      (closedImmersionIdealTwistSequence_shortExact i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)).extClass.comp
        (@SerreExtensionSequenceData.extensionClass.{u} (hypersurface p hp) _ e.toSequenceData hExt)
        (show 1 + 1 = 2 by omega) ≠ 0)
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (hL : Module.finrank K L = 11)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp)
      (show (hypersurface p hp).Modules from e.E))]
    (C : SerreExtensionRankTwoAffineCover e)
    (j₃ : Spec (.of L₃) ⟶ hypersurface p hp) [IsClosedImmersion j₃]
    (hj₃ : j₃ ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L₃)))
    (hL₃ : Module.finrank K L₃ = 3)
    (cfg : B ⟶ Spec (.of K))
    (marked : Fin 3 → (B ⟶ hypersurface p hp))
    (hm : ∀ n, marked n ≫ hypersurfaceToBase p hp = cfg) :
    let base := hypersurfaceToBase p hp
    let M : (hypersurface p hp).Modules := e.E
    let pp := schemeModuleGlobalSectionsProjectiveParametersToBase base M
    let D := serreIncidenceRankTwoAffineCover e C
    let zero := D.projectiveSectionLocalZeroGluedToAmbient base M
    letI : IsClosedImmersion zero := D.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
    letI : IsProper (zero ≫ pullback.snd base pp) := serreSectionUniversalZeroToParameters_isProper base M D
    let g := serreThreePointSectionIncidenceZeroFamily cfg base pp marked hm zero
    ∀ (t : Spec (.of K) ⟶ schemeModuleGlobalSectionsProjectiveParameters base M),
      t ≫ pp = 𝟙 _ →
      ∀ (s : Spec (.of E) ⟶ serreThreePointSectionIncidence cfg base pp marked hm zero),
      s (IsLocalRing.closedPoint E) ∈
        cubicClosedPointSerreFiniteZeroResidual_goodOpen g ⊓
        cubicClosedPointSerreFiniteZeroResidual_incidenceMarkedOpen cfg base pp marked hm zero →
      s ≫ serreThreePointSectionIncidenceToParameters cfg base pp marked hm zero =
        Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫ t →
      ∀ n : Fin 3,
      (s ≫ serreThreePointSectionIncidenceToConfiguration cfg base pp marked hm zero ≫ marked n)
        (IsLocalRing.closedPoint E) ∉ Set.range i →
      (s ≫ serreThreePointSectionIncidenceToConfiguration cfg base pp marked hm zero ≫ marked n)
        (IsLocalRing.closedPoint E) = j₃ (IsLocalRing.closedPoint L₃) →
      ∃ R : AllCharacteristics.FiniteSubschemeDatum base 8,
        Disjoint (Set.range R.val.subschemeι) (Set.range j₃) := by
  let base := hypersurfaceToBase p hp
  let M : (hypersurface p hp).Modules := e.E
  let pp := schemeModuleGlobalSectionsProjectiveParametersToBase base M
  let D := serreIncidenceRankTwoAffineCover e C
  let zero := D.projectiveSectionLocalZeroGluedToAmbient base M
  letI : IsClosedImmersion zero := D.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
  letI : IsProper (zero ≫ pullback.snd base pp) := serreSectionUniversalZeroToParameters_isProper base M D
  dsimp only
  intro t ht s hW hsp n hout hsupport
  obtain ⟨seed,j,b,a,ha,hb,hbt,hlift,hc⟩ :=
    cubicClosedPointSerreFiniteZeroResidual_original_chosen_parameter_exists_seed
      K p hp hp0 i e hne C cfg marked hm t ht s hsp n hout
  have hsp' : s ≫ serreThreePointSectionIncidenceToParameters cfg base pp marked hm zero =
      Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫ serreIncidenceGroundSectionParameter base M j b := by
    rw [hbt]
    exact hsp
  let c := C.localPencilZeroGluedToAmbient e seed 0 (𝟙 _)
  letI : IsClosedImmersion c :=
    C.isClosedImmersion_localPencilZeroGluedToAmbient_of_localPencilZeroGluing e seed 0 (𝟙 _)
  have hf := cubicClosedPointSerreFiniteZeroResidual_selected_chart_goodPoint_endpoint_finite
    base e C seed cfg marked hm j b hb a ha hc s hW.1 hsp'
  letI : IsFinite (c ≫ base) :=
    (cubicClosedPointSerreFiniteZeroResidual_selected_finite_rank_eleven
      K p hp hp0 i e hne hi hL C seed hf).1
  obtain ⟨ht',v,hv,hvc⟩ :=
    cubicClosedPointSerreFiniteZeroResidual_selected_chart_parameter_surface_fibre base e C seed j b hb a ha hc
  have hmrange := cubicClosedPointSerreFiniteZeroResidual_chosenMarked_mem_surface_range
    cfg base pp marked hm zero s (serreIncidenceGroundSectionParameter base M j b)
    (c ≫ base) c v hv hvc (Spec.map (CommRingCat.ofHom (algebraMap K E))) hsp' n
    (IsLocalRing.closedPoint E)
  have hjrange : j₃ (IsLocalRing.closedPoint L₃) ∈ Set.range c := hsupport ▸ hmrange
  let w := cubicClosedPointSerreFiniteZeroResidual_fieldPoint_support_embedding c j₃ hjrange
  letI : IsClosedImmersion w :=
    cubicClosedPointSerreFiniteZeroResidual_fieldPoint_support_embedding_isClosedImmersion c j₃ hjrange
  have hwc : w ≫ c = j₃ :=
    cubicClosedPointSerreFiniteZeroResidual_fieldPoint_support_embedding_comp c j₃ hjrange
  have hpoint : (s ≫ serreThreePointSectionIncidenceToConfiguration cfg base pp marked hm zero ≫ marked n)
      (IsLocalRing.closedPoint E) = c (w (IsLocalRing.closedPoint L₃)) := by
    rw [hsupport,← hwc,Scheme.Hom.comp_apply]
  letI : IsFinite (j₃ ≫ base) := by
    rw [hj₃]
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have hthree : finiteSchemeRank (w ≫ c ≫ base) = 3 := by
    rw [finiteSchemeRank_eq_finrank,← Category.assoc,hwc,hj₃,
      Scheme.Hom.finrank_SpecMap_algebraMap]
    exact (congrFun (Module.rankAtStalk_eq_finrank_of_free (R := K) (M := L₃))
      (IsLocalRing.closedPoint K)).trans hL₃
  have H := cubicClosedPointSerreFiniteZeroResidual_original_good_selected_incidence_datum_eight
    K p hp hp0 i e hne hi hL C seed cfg marked hm j b hb a ha hc
    s hW hsp' n w hpoint hthree
  change ∃ R : AllCharacteristics.FiniteSubschemeDatum base 8,
    Disjoint (Set.range R.val.subschemeι) (Set.range (w ≫ c)) at H
  simpa only [hwc] using H

end PfaffianDescent.ProjectiveNegativeTwist
