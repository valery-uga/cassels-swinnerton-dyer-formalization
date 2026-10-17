import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGroundZeroKernel
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNormalizedGroundParameter
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceSurfaceScaleCoordinates
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualCanonicalNonzero

/-! # Native normalized canonical graphs preserve the actual canonical zero ideal -/
noncomputable section
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceCanonicalSection_exists_ground_graph_kernel
    {K : Type u} [Field K] {X Z : Scheme.{u}} {N : X.Modules}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (e : SerreExtensionData X N)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))]
    (x : X) {ι : Type u} [Fintype ι] [DecidableEq ι]
    (C : SchemeModuleFiniteFreeAffineCover (show X.Modules from e.E) ι)
    (i : Z ⟶ X)
    (hlocal : ∀ k, localSectionZeroIdealOfOver (C.U k) ι
      (C.trivialization k) e.canonicalSection = i.ker.comap (C.U k).ι) :
    ∃ (j : Fin (Module.finrank K
      (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))))
      (b : finiteDimensionalProjectiveChartRing K
        (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E)) j →+* K)
      (hb : b.comp (chartBaseMap (finiteDimensionalProjectiveIdeal K
        (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))) j) = RingHom.id K),
      (C.projectiveSectionLocalZeroGluedToAmbient base (show X.Modules from e.E)).ker.comap
        (serreIncidenceGroundSectionGraph base (show X.Modules from e.E) j b hb) = i.ker := by
  let s : SchemeModuleGlobalSectionsOver base (show X.Modules from e.E) := e.inclusion
  obtain ⟨j,b,a,ha,hb,hc⟩ := serreIncidenceSection_exists_normalized_ground_parameter
    base (show X.Modules from e.E) s
      (cubicClosedPointSerreFiniteZeroResidual_canonicalGlobalSection_nonzero e x)
  refine ⟨j,b,hb,serreIncidenceGroundSectionGraph_kernel_eq base
    (show X.Modules from e.E) j b hb (a • s) hc C i ?_⟩
  intro k
  exact (serreIncidenceSurfaceSectionZeroIdeal_smul_unit base (show X.Modules from e.E)
    (C.U k) ι (localFreeIsoOfOver (C.U k) ι (C.trivialization k))
    a ha s).trans (hlocal k)

end PfaffianDescent
