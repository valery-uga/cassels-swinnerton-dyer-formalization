import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGroundZeroChart
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualIdealCover

/-! # Gluing actual section-graph zero ideals over the surface -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceGroundSectionGraph_kernel_eq
    {K : Type u} [Field K] {X Z : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M)))
    (b : finiteDimensionalProjectiveChartRing K (SchemeModuleGlobalSectionsOver base M) j →+* K)
    (hb : b.comp (chartBaseMap (finiteDimensionalProjectiveIdeal K
      (SchemeModuleGlobalSectionsOver base M)) j) = RingHom.id K)
    (s : SchemeModuleGlobalSectionsOver base M)
    (hcoordinates : ∀ k, b (chartCoordinate (finiteDimensionalProjectiveIdeal K
      (SchemeModuleGlobalSectionsOver base M)) j k) =
      (Module.finBasis K (SchemeModuleGlobalSectionsOver base M)).repr s k)
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (C : SchemeModuleFiniteFreeAffineCover M ι) (i : Z ⟶ X)
    (hlocal : ∀ k, sectionZeroIdealOfFreeIso ι
      (localFreeIsoOfOver (C.U k) ι (C.trivialization k))
      (restrictSectionToOpen (C.U k)
        (schemeModuleGlobalSectionsOverEquivSections base M s)) = i.ker.comap (C.U k).ι) :
    (C.projectiveSectionLocalZeroGluedToAmbient base M).ker.comap
      (serreIncidenceGroundSectionGraph base M j b hb) = i.ker := by
  apply cubicClosedPointSerreFiniteZeroResidual_ideal_eq_of_affine_pullbacks
    _ _ (fun k => ⟨C.U k, C.affine k⟩) C.covers
  intro k
  rw [← Scheme.IdealSheafData.comap_comp,
    ← serreIncidenceGroundSectionChartGraph_comp base M j b hb C k]
  exact (serreIncidenceGroundSectionChartGraph_zeroIdeal base M j b hb s
    hcoordinates C k).trans (hlocal k)

end PfaffianDescent
