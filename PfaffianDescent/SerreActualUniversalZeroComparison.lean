import PfaffianDescent.SerreActualPulledSectionZeroIdeal
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceUniversalZeroIdealChart

/-! Comparing actual local universal sections compares the actual globally
glued universal zero ideals on the common affine source. An invertible
normalizing coefficient changes no scheme structure. -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreActualUniversalZero_comap_chart_eq_of_section_unit_scale
    {K L : Type u} [Field K] [Field L] {X Y T : Scheme.{u}} [IsAffine T]
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    (base' : Y ⟶ Spec (.of L)) [IsSeparated base'] (N : Y.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    [FiniteDimensional L (SchemeModuleGlobalSectionsOver base' N)]
    {ι κ : Type u} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (C : SchemeModuleFiniteFreeAffineCover M ι)
    (D : SchemeModuleFiniteFreeAffineCover N κ)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    (kl : (D.projectiveSectionOpenCover base' N).I₀)
    (f : T ⟶ (C.projectiveSectionOpenCover base M).X ij)
    (g : T ⟶ (D.projectiveSectionOpenCover base' N).X kl)
    (e : (Scheme.Modules.pullback f).obj (C.projectiveSectionLocalModule base M ij) ≅
      (Scheme.Modules.pullback g).obj (D.projectiveSectionLocalModule base' N kl))
    (a : Γ(T, ⊤)) (ha : IsUnit a)
    (hsections : SheafOfModules.sectionsMap e.hom
      (pullbackSection f (C.projectiveSectionLocalModule base M ij)
        (isIso_pullbackUnitComparison f) (C.projectiveSectionLocalUniversalSection base M ij)) =
      scaleSection (unitEndomorphismOfRegularFunction a)
        (pullbackSection g (D.projectiveSectionLocalModule base' N kl)
          (isIso_pullbackUnitComparison g) (D.projectiveSectionLocalUniversalSection base' N kl))) :
    (C.projectiveSectionLocalZeroGluedToAmbient base M).ker.comap
        (f ≫ (C.projectiveSectionOpenCover base M).f ij) =
      (D.projectiveSectionLocalZeroGluedToAmbient base' N).ker.comap
        (g ≫ (D.projectiveSectionOpenCover base' N).f kl) := by
  rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp,
    serreIncidenceUniversalZeroIdeal_comap_chart, serreIncidenceUniversalZeroIdeal_comap_chart]
  exact serreActualPulledSectionZeroIdeal_eq_of_iso_unit_scale f g
    (C.projectiveSectionLocalFreeIso base M ij) (D.projectiveSectionLocalFreeIso base' N kl)
    (C.projectiveSectionLocalUniversalSection base M ij)
    (D.projectiveSectionLocalUniversalSection base' N kl) e a ha hsections

end PfaffianDescent
