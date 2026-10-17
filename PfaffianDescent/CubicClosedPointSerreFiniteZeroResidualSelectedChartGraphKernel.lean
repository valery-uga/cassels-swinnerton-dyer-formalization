import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNormalizedEndpointKernel
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGroundZeroKernel
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNormalizedGroundParameter
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceSurfaceScaleCoordinates
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNativeMatrix

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open BundleSectionZeroLocus SerreExtensionData
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_selected_chart_graph_kernel
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
    let D := serreIncidenceRankTwoAffineCover e C
    (D.projectiveSectionLocalZeroGluedToAmbient base (show X.Modules from e.E)).ker.comap
      (serreIncidenceGroundSectionGraph base (show X.Modules from e.E) j b hb) =
    (C.localPencilZeroGluedToAmbient e seed 0 (𝟙 _)).ker := by
  let s : SchemeModuleGlobalSectionsOver base (show X.Modules from e.E) :=
    e.E.unitHomEquiv.symm seed.lift
  let D := serreIncidenceRankTwoAffineCover e C
  apply serreIncidenceGroundSectionGraph_kernel_eq base
    (show X.Modules from e.E) j b hb (a • s) hc D
    (C.localPencilZeroGluedToAmbient e seed 0 (𝟙 _))
  intro k
  refine (serreIncidenceSurfaceSectionZeroIdeal_smul_unit base (show X.Modules from e.E)
    (D.U k) (ULift.{u} (Fin 2))
    (localFreeIsoOfOver (D.U k) (ULift.{u} (Fin 2)) (D.trivialization k))
    a ha s).trans ?_
  change sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2))
    (localFreeIsoOfOver (C.U k) (ULift.{u} (Fin 2)) (C.trivialization k))
    (restrictSectionToOpen (C.U k) (e.E.unitHomEquiv (e.E.unitHomEquiv.symm seed.lift))) = _
  rw [Equiv.apply_symm_apply]
  exact (C.localPencilZeroIdeal_zero_one e seed k).symm.trans
    (cubicClosedPointSerreFiniteZeroResidual_localGlued_kernel_comap C seed k 0 (𝟙 _)).symm

end PfaffianDescent
