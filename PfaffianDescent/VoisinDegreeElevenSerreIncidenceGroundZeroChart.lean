import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGroundSectionCoefficients
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceSurfaceBasisCoordinates

/-! # Actual universal-zero specialization to the actual ground section -/
noncomputable section
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

/-- Along the actual graph of a ground section parameter with its literal
basis coordinates, the actual global universal-zero ideal is the actual
section zero ideal on every surface trivialization. -/
theorem serreIncidenceGroundSectionChartGraph_zeroIdeal
    {K : Type u} [Field K] {X : Scheme.{u}}
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
    (C : SchemeModuleFiniteFreeAffineCover M ι) (i : C.ι) :
    (C.projectiveSectionLocalZeroGluedToAmbient base M).ker.comap
      (serreIncidenceGroundSectionChartGraph base M j b hb C i ≫
        (C.projectiveSectionOpenCover base M).f (i,j)) =
    sectionZeroIdealOfFreeIso ι
      (localFreeIsoOfOver (C.U i) ι (C.trivialization i))
      (restrictSectionToOpen (C.U i) (schemeModuleGlobalSectionsOverEquivSections base M s)) := by
  letI : IsAffine (C.U i : Scheme.{u}) := C.affine i
  let f := serreIncidenceGroundSectionChartGraph base M j b hb C i
  have h := serreIncidenceUniversalZeroIdeal_comap_linearEquations base M C (i,j) f
  refine h.trans ?_
  unfold sectionZeroIdealOfFreeIso freeSectionZeroIdeal
  congr 2
  apply congrArg Set.range
  funext a
  have hc : ∀ k, f.appTop (C.projectiveSectionLocalCoefficient base M (i,j) k) =
      (C.U i).ι.appTop (affineFunctionHom base
        ((Module.finBasis K (SchemeModuleGlobalSectionsOver base M)).repr s k)) := by
    intro k
    rw [serreIncidenceGroundSectionChartGraph_coefficient, hcoordinates k,
      affineFunctionHom_comp]
    rfl
  have he : ∀ k, serreUniversalChartEvaluationCoordinate base M C (i,j) f a k =
      sectionCoordinateOfFreeIso ι
        (localFreeIsoOfOver (C.U i) ι (C.trivialization i))
        (restrictSectionToOpen (C.U i) (schemeModuleGlobalSectionsOverEquivSections base M
          (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) k))) a := by
    intro k
    have he := serreUniversalChartEvaluationCoordinate_eq_configuration base M C (i,j) f
      (𝟙 (C.U i : Scheme.{u})) (𝟙 (C.U i : Scheme.{u}))
      (by
        exact (serreIncidenceGroundSectionChartGraph_surface base M j b hb C i).trans
          (Category.id_comp _).symm) a k
    simpa using he
  have hsum := Finset.sum_congr
    (show (Finset.univ : Finset (Fin (Module.finrank K
      (SchemeModuleGlobalSectionsOver base M)))) = Finset.univ from rfl)
    (fun k _ => congrArg₂ (fun x y => x * y) (hc k) (he k))
  exact hsum.trans (serreIncidenceSurfaceBasisCoordinate_reconstruct base M (C.U i) ι
    (localFreeIsoOfOver (C.U i) ι (C.trivialization i)) s a)

end PfaffianDescent
