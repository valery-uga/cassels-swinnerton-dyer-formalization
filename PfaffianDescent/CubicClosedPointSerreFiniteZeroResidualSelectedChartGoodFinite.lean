import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualSelectedChartSurfaceFibre
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualGoodPointFinite
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceSeedFibre

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
open BundleSectionZeroLocus AllCharacteristics.HomogeneousProjective SerreExtensionData
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_selected_chart_goodPoint_endpoint_finite
    {K E : Type u} [Field K] [Field E] [Algebra K E] {X B : Scheme.{u}} {N : X.Modules}
    (base : X ⟶ Spec (.of K)) [IsProper base] (e : SerreExtensionData X N)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))]
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (cfg : B ⟶ Spec (.of K))
    (marked : Fin 3 → (B ⟶ X)) (hm : ∀ n, marked n ≫ base = cfg)
    (j : Fin (Module.finrank K
      (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))))
    (b : finiteDimensionalProjectiveChartRing K
      (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E)) j →+* K)
    (hb : b.comp (chartBaseMap (finiteDimensionalProjectiveIdeal K
      (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))) j) = RingHom.id K)
    (a : K) (ha : IsUnit a)
    (hc : let s : SchemeModuleGlobalSectionsOver base (show X.Modules from e.E) :=
      e.E.unitHomEquiv.symm seed.lift
      ∀ k, b (chartCoordinate (finiteDimensionalProjectiveIdeal K
      (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))) j k) =
      (Module.finBasis K (SchemeModuleGlobalSectionsOver base
        (show X.Modules from e.E))).repr
          (a • s) k) :
    let M : X.Modules := e.E
    let D := serreIncidenceRankTwoAffineCover e C
    let p := schemeModuleGlobalSectionsProjectiveParametersToBase base M
    let zero := D.projectiveSectionLocalZeroGluedToAmbient base M
    letI : IsClosedImmersion zero := D.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
    letI : IsProper (zero ≫ pullback.snd base p) := serreSectionUniversalZeroToParameters_isProper base M D
    let g := serreThreePointSectionIncidenceZeroFamily cfg base p marked hm zero
    let t := serreIncidenceGroundSectionParameter base M j b
    ∀ (s : Spec (.of E) ⟶ serreThreePointSectionIncidence cfg base p marked hm zero),
      s (IsLocalRing.closedPoint E) ∈ cubicClosedPointSerreFiniteZeroResidual_goodOpen g →
      s ≫ serreThreePointSectionIncidenceToParameters cfg base p marked hm zero =
        Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫ t →
      ((C.projectiveLineNormalizedLocalPencilZeroGluedToAmbient base seed ≫
        projectiveLineAmbientToLine K base) ⁻¹'
          {projectiveLineEndpoint K true (IsLocalRing.closedPoint K)}).Finite := by
  let M : X.Modules := e.E
  let D := serreIncidenceRankTwoAffineCover e C
  let p := schemeModuleGlobalSectionsProjectiveParametersToBase base M
  let zero := D.projectiveSectionLocalZeroGluedToAmbient base M
  letI : IsClosedImmersion zero := D.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
  letI : IsProper (zero ≫ pullback.snd base p) := serreSectionUniversalZeroToParameters_isProper base M D
  let g := serreThreePointSectionIncidenceZeroFamily cfg base p marked hm zero
  let t := serreIncidenceGroundSectionParameter base M j b
  let c := C.localPencilZeroGluedToAmbient e seed 0 (𝟙 _)
  let r := Spec.map (CommRingCat.ofHom (algebraMap K E))
  dsimp only
  intro s hs hsp
  obtain ⟨ht,v,hv,hvc⟩ := cubicClosedPointSerreFiniteZeroResidual_selected_chart_parameter_surface_fibre
    base e C seed j b hb a ha hc
  let w := serreIncidenceSeedCanonicalFibreIso cfg base p marked hm zero s t (c ≫ base) v hv r hsp
  letI : Finite (pullback g s : Scheme) :=
    cubicClosedPointSerreFiniteZeroResidual_goodOpen_fieldPoint_finite g s hs
  letI : Finite (pullback (c ≫ base) r : Scheme) := Finite.of_injective w.hom w.hom.injective
  letI : Finite (C.localPencilZeroGluedScheme e seed 0 (𝟙 _) : Scheme) :=
    cubicClosedPointSerreFiniteZeroResidual_fieldBaseChange_finite_descend (E := E) (c ≫ base)
  exact cubicClosedPointSerreFiniteZeroResidual_normalizedSelected_endpoint_finite base e C seed

end PfaffianDescent
