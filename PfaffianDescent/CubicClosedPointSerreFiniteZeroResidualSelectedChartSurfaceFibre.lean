import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualSelectedChartGraphKernel
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceClosedGraphSurface

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
open BundleSectionZeroLocus AllCharacteristics.HomogeneousProjective SerreExtensionData
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_selected_chart_parameter_surface_fibre
    {K : Type u} [Field K] {X : Scheme.{u}} {N : X.Modules}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (e : SerreExtensionData X N)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))]
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
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
    let zero := D.projectiveSectionLocalZeroGluedToAmbient base M
    let z := zero ≫ pullback.snd base
      (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
    let i := C.localPencilZeroGluedToAmbient e seed 0 (𝟙 _)
    let t := serreIncidenceGroundSectionParameter base M j b;
      t ≫ schemeModuleGlobalSectionsProjectiveParametersToBase base M = 𝟙 _ ∧
      ∃ (v : C.localPencilZeroGluedScheme e seed 0 (𝟙 _) ≅ pullback z t),
        v.hom ≫ pullback.snd z t = i ≫ base ∧
        v.hom ≫ pullback.fst z t ≫ zero ≫
          pullback.fst base (schemeModuleGlobalSectionsProjectiveParametersToBase base M) = i := by
  let i := C.localPencilZeroGluedToAmbient e seed 0 (𝟙 _)
  letI : IsClosedImmersion i :=
    C.isClosedImmersion_localPencilZeroGluedToAmbient_of_localPencilZeroGluing e seed 0 (𝟙 _)
  let M : X.Modules := e.E
  let D := serreIncidenceRankTwoAffineCover e C
  let zero := D.projectiveSectionLocalZeroGluedToAmbient base M
  letI : IsClosedImmersion zero :=
    D.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
  have hk := cubicClosedPointSerreFiniteZeroResidual_selected_chart_graph_kernel
    base e C seed j b hb a ha hc
  let t := serreIncidenceGroundSectionParameter base M j b
  have ht : t ≫ schemeModuleGlobalSectionsProjectiveParametersToBase base M = 𝟙 _ :=
    serreIncidenceGroundSectionParameter_toBase base M j b hb
  let g := serreIncidenceGroundSectionGraph base M j b hb
  let v := serreIncidenceClosedGraphZeroIso base
    (schemeModuleGlobalSectionsProjectiveParametersToBase base M) t ht g
    (serreIncidenceGroundSectionGraph_fst base M j b hb)
    (serreIncidenceGroundSectionGraph_snd base M j b hb) zero i hk
  refine ⟨ht,v,?_,?_⟩
  · exact serreIncidenceClosedGraphZeroIso_hom_snd base
      (schemeModuleGlobalSectionsProjectiveParametersToBase base M) t ht g
      (serreIncidenceGroundSectionGraph_fst base M j b hb)
      (serreIncidenceGroundSectionGraph_snd base M j b hb) zero i hk
  · exact serreIncidenceClosedGraphZeroIso_hom_surface base
      (schemeModuleGlobalSectionsProjectiveParametersToBase base M) t ht g
      (serreIncidenceGroundSectionGraph_fst base M j b hb)
      (serreIncidenceGroundSectionGraph_snd base M j b hb) zero i hk

end PfaffianDescent
