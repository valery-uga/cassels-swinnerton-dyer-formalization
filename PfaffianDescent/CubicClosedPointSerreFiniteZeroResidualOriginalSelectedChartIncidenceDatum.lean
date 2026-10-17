import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualSelectedChartIncidenceDatum
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualSelectedRankEleven

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AllCharacteristics
namespace PfaffianDescent.ProjectiveNegativeTwist
open BundleSectionZeroLocus AllCharacteristics.HomogeneousProjective SerreExtensionData
open PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_original_selected_chart_incidence_datum_eight
    (K : Type u) [Field K] {E L₃ : Type u} [Field E] [Field L₃] [Algebra K E]
    {B : Scheme.{u}}
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
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (hf : ((C.projectiveLineNormalizedLocalPencilZeroGluedToAmbient (hypersurfaceToBase p hp) seed ≫
      projectiveLineAmbientToLine K (hypersurfaceToBase p hp)) ⁻¹'
        {projectiveLineEndpoint K true (IsLocalRing.closedPoint K)}).Finite)
    (cfg : B ⟶ Spec (.of K))
    (marked : Fin 3 → (B ⟶ hypersurface p hp)) (hm : ∀ n, marked n ≫ (hypersurfaceToBase p hp) = cfg)
    (j : Fin (Module.finrank K
      (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) (show (hypersurface p hp).Modules from e.E))))
    (b : finiteDimensionalProjectiveChartRing K
      (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) (show (hypersurface p hp).Modules from e.E)) j →+* K)
    (hb : b.comp (chartBaseMap (finiteDimensionalProjectiveIdeal K
      (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) (show (hypersurface p hp).Modules from e.E))) j) = RingHom.id K)
    (a : K) (ha : IsUnit a)
    (hc : let s : SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) (show (hypersurface p hp).Modules from e.E) :=
      e.E.unitHomEquiv.symm seed.lift
      ∀ k, b (chartCoordinate (finiteDimensionalProjectiveIdeal K
      (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) (show (hypersurface p hp).Modules from e.E))) j k) =
      (Module.finBasis K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp)
        (show (hypersurface p hp).Modules from e.E))).repr
          (a • s) k) :
    let M : (hypersurface p hp).Modules := e.E
    let D := serreIncidenceRankTwoAffineCover e C
    let pp := schemeModuleGlobalSectionsProjectiveParametersToBase (hypersurfaceToBase p hp) M
    let zero := D.projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) M
    letI : IsClosedImmersion zero := D.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient (hypersurfaceToBase p hp) M
    let c := C.localPencilZeroGluedToAmbient e seed 0 (𝟙 _)
    letI : IsFinite (c ≫ hypersurfaceToBase p hp) :=
      (cubicClosedPointSerreFiniteZeroResidual_selected_finite_rank_eleven
        K p hp hp0 i e hne hi hL C seed hf).1
    let t := serreIncidenceGroundSectionParameter (hypersurfaceToBase p hp) M j b
    ∀ (s : Spec (.of E) ⟶ serreThreePointSectionIncidence cfg (hypersurfaceToBase p hp) pp marked hm zero),
      s (IsLocalRing.closedPoint E) ∈
        cubicClosedPointSerreFiniteZeroResidual_incidenceMarkedOpen cfg (hypersurfaceToBase p hp) pp marked hm zero →
      s ≫ serreThreePointSectionIncidenceToParameters cfg (hypersurfaceToBase p hp) pp marked hm zero =
        Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫ t →
      ∀ (n : Fin 3) (i : Spec (.of L₃) ⟶ C.localPencilZeroGluedScheme e seed 0 (𝟙 _))
        [IsClosedImmersion i],
      (s ≫ serreThreePointSectionIncidenceToConfiguration cfg (hypersurfaceToBase p hp) pp marked hm zero ≫
        marked n) (IsLocalRing.closedPoint E) = c (i (IsLocalRing.closedPoint L₃)) →
      finiteSchemeRank (i ≫ c ≫ (hypersurfaceToBase p hp)) = 3 →
      ∃ R : AllCharacteristics.FiniteSubschemeDatum (hypersurfaceToBase p hp) 8,
        Disjoint (Set.range R.val.subschemeι) (Set.range (i ≫ c)) := by
  let base := hypersurfaceToBase p hp
  let M : (hypersurface p hp).Modules := e.E
  let D := serreIncidenceRankTwoAffineCover e C
  let pp := schemeModuleGlobalSectionsProjectiveParametersToBase base M
  let zero := D.projectiveSectionLocalZeroGluedToAmbient base M
  letI : IsClosedImmersion zero := D.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
  let c := C.localPencilZeroGluedToAmbient e seed 0 (𝟙 _)
  have H := cubicClosedPointSerreFiniteZeroResidual_selected_finite_rank_eleven
    K p hp hp0 i e hne hi hL C seed hf
  letI : IsFinite (c ≫ base) := H.1
  dsimp only
  intro s hs hsp n jmark hjmark hpoint hthree
  have h11 : finiteSchemeRank (c ≫ base) = 11 := by
    rw [finiteSchemeRank_eq_finrank]
    exact H.2 (IsLocalRing.closedPoint K)
  exact cubicClosedPointSerreFiniteZeroResidual_selected_chart_incidence_datum_eight
    base e C seed cfg marked hm j b hb a ha hc s hs hsp n jmark hpoint h11 hthree

end PfaffianDescent.ProjectiveNegativeTwist
