import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGlobalBasisCoordinates
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceUniversalLinearEquations

/-! # Universal equation coefficients come from the configuration chart -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- An actual universal-chart coefficient equals the pullback of its actual
surface evaluation function along the marked configuration map. -/
theorem serreUniversalChartEvaluationCoordinate_eq_configuration
    {K : Type u} [Field K] {X A B : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (C : SchemeModuleFiniteFreeAffineCover M ι)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    (f : B ⟶ (C.projectiveSectionOpenCover base M).X ij)
    (d : B ⟶ A) (marked : A ⟶ (C.U ij.1 : Scheme.{u}))
    (hf : f ≫ C.projectiveSectionOpenCoverToSurfaceChart base M ij = d ≫ marked)
    (a : ι) (k : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    serreUniversalChartEvaluationCoordinate base M C ij f a k =
      d.appTop (marked.appTop
        (BundleSectionZeroLocus.sectionCoordinateOfFreeIso ι
          (BundleSectionZeroLocus.localFreeIsoOfOver (C.U ij.1) ι (C.trivialization ij.1))
          (BundleSectionZeroLocus.restrictSectionToOpen (C.U ij.1)
            (schemeModuleGlobalSectionsOverEquivSections base M
              (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) k))) a)) := by
  unfold serreUniversalChartEvaluationCoordinate
  rw [serreIncidenceUniversalBasisCoordinate_eq_surface]
  have h := congrArg (fun t : B ⟶ (C.U ij.1 : Scheme.{u}) => t.appTop) hf
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h
  exact congrArg (fun t => t
    (BundleSectionZeroLocus.sectionCoordinateOfFreeIso ι
      (BundleSectionZeroLocus.localFreeIsoOfOver (C.U ij.1) ι (C.trivialization ij.1))
      (BundleSectionZeroLocus.restrictSectionToOpen (C.U ij.1)
        (schemeModuleGlobalSectionsOverEquivSections base M
          (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) k))) a)) h

end PfaffianDescent
