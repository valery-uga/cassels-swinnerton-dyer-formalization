import PfaffianDescent.VoisinDegreeElevenSerreIncidenceUniversalZeroIdealChart

/-! # Actual linear evaluation equations on universal incidence charts -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- The literal scalar evaluation coefficients of the canonical global
section basis, pulled to an actual affine universal incidence chart. -/
def serreUniversalChartEvaluationCoordinate
    {K : Type u} [Field K] {X B : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (C : SchemeModuleFiniteFreeAffineCover M ι)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    (f : B ⟶ (C.projectiveSectionOpenCover base M).X ij)
    (a : ι) (k : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    Γ(B, ⊤) :=
  f.appTop (BundleSectionZeroLocus.sectionCoordinateOfFreeIso ι
    (C.projectiveSectionLocalFreeIso base M ij)
    (BundleSectionZeroLocus.pullbackSection
      (C.projectiveSectionOpenCoverToSurface base M ij) M
      (BundleSectionZeroLocus.isIso_pullbackUnitComparison _)
      (schemeModuleGlobalSectionsOverEquivSections base M
        (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) k))) a)

/-- The actual pulled-back glued zero ideal has the literal linear equations
in normalized projective coefficients and canonical basis evaluations. -/
theorem serreIncidenceUniversalZeroIdeal_comap_linearEquations
    {K : Type u} [Field K] {X B : Scheme.{u}} [IsAffine B]
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (C : SchemeModuleFiniteFreeAffineCover M ι)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    (f : B ⟶ (C.projectiveSectionOpenCover base M).X ij) :
    (C.projectiveSectionLocalZeroGluedToAmbient base M).ker.comap
        (f ≫ (C.projectiveSectionOpenCover base M).f ij) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.span (Set.range fun a : ι =>
        ∑ k, f.appTop (C.projectiveSectionLocalCoefficient base M ij k) *
          serreUniversalChartEvaluationCoordinate base M C ij f a k)) := by
  rw [serreIncidenceUniversalZeroIdeal_comap_affineChart]
  congr 2
  apply congrArg Set.range
  funext a
  rw [C.projectiveSectionLocalUniversalSectionCoordinate_eq_sum base M ij a,
    map_sum]
  simp only [map_mul, serreUniversalChartEvaluationCoordinate]

end PfaffianDescent
