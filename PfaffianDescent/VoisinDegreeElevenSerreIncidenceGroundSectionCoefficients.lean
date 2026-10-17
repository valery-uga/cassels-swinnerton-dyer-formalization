import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGroundSectionGraph

/-! # Literal section-coordinate specialization on the actual ground graph -/
noncomputable section
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual universal coefficient on the graph of the ground section
parameter is the corresponding literal constant regular function. -/
theorem serreIncidenceGroundSectionChartGraph_coefficient
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M)))
    (b : finiteDimensionalProjectiveChartRing K (SchemeModuleGlobalSectionsOver base M) j →+* K)
    (hb : b.comp (chartBaseMap (finiteDimensionalProjectiveIdeal K
      (SchemeModuleGlobalSectionsOver base M)) j) = RingHom.id K)
    {ι : Type u} (C : SchemeModuleFiniteFreeAffineCover M ι) (i : C.ι)
    (k : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    (serreIncidenceGroundSectionChartGraph base M j b hb C i).appTop
      (C.projectiveSectionLocalCoefficient base M (i,j) k) =
    affineFunctionHom ((C.U i).ι ≫ base)
      (b (chartCoordinate (finiteDimensionalProjectiveIdeal K
        (SchemeModuleGlobalSectionsOver base M)) j k)) := by
  unfold SchemeModuleFiniteFreeAffineCover.projectiveSectionLocalCoefficient
  change affineFunctionHom
    (serreIncidenceGroundSectionChartGraph base M j b hb C i ≫
      C.projectiveSectionOpenCoverToParameterChart base M (i,j))
    (chartCoordinate (finiteDimensionalProjectiveIdeal K
      (SchemeModuleGlobalSectionsOver base M)) j k) = _
  rw [serreIncidenceGroundSectionChartGraph_parameter]
  exact RingHom.congr_fun (affineFunctionHom_comp_Spec ((C.U i).ι ≫ base) b) _

end PfaffianDescent
