import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualOriginalSelectedChartIncidenceDatum
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualSelectedChartGoodFinite
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualSelectedRankEleven

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AllCharacteristics
namespace PfaffianDescent.ProjectiveNegativeTwist
open BundleSectionZeroLocus AllCharacteristics.HomogeneousProjective SerreExtensionData
open PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_original_good_selected_incidence_datum_eight
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
    let base := hypersurfaceToBase p hp
    let M : (hypersurface p hp).Modules := e.E
    let D := serreIncidenceRankTwoAffineCover e C
    let pp := schemeModuleGlobalSectionsProjectiveParametersToBase base M
    let zero := D.projectiveSectionLocalZeroGluedToAmbient base M
    letI : IsClosedImmersion zero := D.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
    letI : IsProper (zero ≫ pullback.snd base pp) := serreSectionUniversalZeroToParameters_isProper base M D
    let g := serreThreePointSectionIncidenceZeroFamily cfg base pp marked hm zero
    let c := C.localPencilZeroGluedToAmbient e seed 0 (𝟙 _)
    let t := serreIncidenceGroundSectionParameter base M j b
    ∀ (s : Spec (.of E) ⟶ serreThreePointSectionIncidence cfg base pp marked hm zero)
      (hW : s (IsLocalRing.closedPoint E) ∈
        cubicClosedPointSerreFiniteZeroResidual_goodOpen g ⊓
        cubicClosedPointSerreFiniteZeroResidual_incidenceMarkedOpen cfg base pp marked hm zero)
      (hsp : s ≫ serreThreePointSectionIncidenceToParameters cfg base pp marked hm zero =
        Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫ t),
    let hf := cubicClosedPointSerreFiniteZeroResidual_selected_chart_goodPoint_endpoint_finite
      base e C seed cfg marked hm j b hb a ha hc s hW.1 hsp
    letI : IsFinite (c ≫ base) :=
      (cubicClosedPointSerreFiniteZeroResidual_selected_finite_rank_eleven
        K p hp hp0 i e hne hi hL C seed hf).1
    ∀ (n : Fin 3) (jmark : Spec (.of L₃) ⟶ C.localPencilZeroGluedScheme e seed 0 (𝟙 _))
      [IsClosedImmersion jmark],
      (s ≫ serreThreePointSectionIncidenceToConfiguration cfg base pp marked hm zero ≫
        marked n) (IsLocalRing.closedPoint E) = c (jmark (IsLocalRing.closedPoint L₃)) →
      finiteSchemeRank (jmark ≫ c ≫ base) = 3 →
      ∃ R : AllCharacteristics.FiniteSubschemeDatum base 8,
        Disjoint (Set.range R.val.subschemeι) (Set.range (jmark ≫ c)) := by
  let base := hypersurfaceToBase p hp
  let M : (hypersurface p hp).Modules := e.E
  let D := serreIncidenceRankTwoAffineCover e C
  let pp := schemeModuleGlobalSectionsProjectiveParametersToBase base M
  let zero := D.projectiveSectionLocalZeroGluedToAmbient base M
  letI : IsClosedImmersion zero := D.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
  letI : IsProper (zero ≫ pullback.snd base pp) := serreSectionUniversalZeroToParameters_isProper base M D
  dsimp only
  intro s hW hsp
  have hf := cubicClosedPointSerreFiniteZeroResidual_selected_chart_goodPoint_endpoint_finite
    base e C seed cfg marked hm j b hb a ha hc s hW.1 hsp
  let c := C.localPencilZeroGluedToAmbient e seed 0 (𝟙 _)
  letI : IsFinite (c ≫ base) :=
    (cubicClosedPointSerreFiniteZeroResidual_selected_finite_rank_eleven
      K p hp hp0 i e hne hi hL C seed hf).1
  intro n jmark hjmark hpoint hthree
  exact cubicClosedPointSerreFiniteZeroResidual_original_selected_chart_incidence_datum_eight
    K p hp hp0 i e hne hi hL C seed hf cfg marked hm j b hb a ha hc
    s hW.2 hsp n jmark hpoint hthree

end PfaffianDescent.ProjectiveNegativeTwist
