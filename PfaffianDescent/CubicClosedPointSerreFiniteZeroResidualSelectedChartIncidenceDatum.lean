import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualSelectedChartSurfaceFibre
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualSelectedIncidenceDatum
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceClosedGraphSurface

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
open AllCharacteristics
open BundleSectionZeroLocus AllCharacteristics.HomogeneousProjective SerreExtensionData
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_selected_chart_incidence_datum_eight
    {K E L : Type u} [Field K] [Field E] [Field L] [Algebra K E]
    {X B : Scheme.{u}} {N : X.Modules}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (e : SerreExtensionData X N)
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
    let c := C.localPencilZeroGluedToAmbient e seed 0 (𝟙 _)
    let t := serreIncidenceGroundSectionParameter base M j b
    ∀ (s : Spec (.of E) ⟶ serreThreePointSectionIncidence cfg base p marked hm zero),
      s (IsLocalRing.closedPoint E) ∈
        cubicClosedPointSerreFiniteZeroResidual_incidenceMarkedOpen cfg base p marked hm zero →
      s ≫ serreThreePointSectionIncidenceToParameters cfg base p marked hm zero =
        Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫ t →
      ∀ (n : Fin 3) (i : Spec (.of L) ⟶ C.localPencilZeroGluedScheme e seed 0 (𝟙 _))
        [IsClosedImmersion i] [IsFinite (c ≫ base)],
      (s ≫ serreThreePointSectionIncidenceToConfiguration cfg base p marked hm zero ≫
        marked n) (IsLocalRing.closedPoint E) = c (i (IsLocalRing.closedPoint L)) →
      finiteSchemeRank (c ≫ base) = 11 →
      finiteSchemeRank (i ≫ c ≫ base) = 3 →
      ∃ R : AllCharacteristics.FiniteSubschemeDatum base 8,
        Disjoint (Set.range R.val.subschemeι) (Set.range (i ≫ c)) := by
  let M : X.Modules := e.E
  let D := serreIncidenceRankTwoAffineCover e C
  let p := schemeModuleGlobalSectionsProjectiveParametersToBase base M
  let zero := D.projectiveSectionLocalZeroGluedToAmbient base M
  letI : IsClosedImmersion zero := D.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
  let c := C.localPencilZeroGluedToAmbient e seed 0 (𝟙 _)
  letI : IsClosedImmersion c :=
    C.isClosedImmersion_localPencilZeroGluedToAmbient_of_localPencilZeroGluing e seed 0 (𝟙 _)
  dsimp only
  intro s hs hsp n i hi hfin hp hX hL
  obtain ⟨ht,v,hv,hvc⟩ :=
    cubicClosedPointSerreFiniteZeroResidual_selected_chart_parameter_surface_fibre
      base e C seed j b hb a ha hc
  exact cubicClosedPointSerreFiniteZeroResidual_selected_incidence_datum_eight
    cfg base p marked hm zero s hs n i c
    (serreIncidenceGroundSectionParameter base M j b) v hv hvc hsp hp hX hL

end PfaffianDescent
