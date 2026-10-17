import PfaffianDescent.SerreActualUniversalZeroComparison

/-! Compare the two actual universal sections through their actual
isomorphisms to a common pulled-back module. This constructs the comparison
isomorphism required by the zero-ideal theorem. -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreActualSection_commonModule_unit_scale
    {T : Scheme.{u}} {M N P : T.Modules}
    (e : M ≅ P) (d : N ≅ P) (s : M.sections) (v : N.sections)
    (a : Γ(T, ⊤))
    (h : SheafOfModules.sectionsMap e.hom s =
      scaleSection (unitEndomorphismOfRegularFunction a)
        (SheafOfModules.sectionsMap d.hom v)) :
    SheafOfModules.sectionsMap (e ≪≫ d.symm).hom s =
      scaleSection (unitEndomorphismOfRegularFunction a) v := by
  rw [Iso.trans_hom, Iso.symm_hom, SheafOfModules.sectionsMap_comp, h,
    sectionsMap_scaleSection, ← SheafOfModules.sectionsMap_comp]
  simp only [Iso.hom_inv_id, SheafOfModules.sectionsMap_id]

theorem serreActualUniversalZero_commonModule_comap_chart_eq
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
    {P : T.Modules}
    (e : (Scheme.Modules.pullback f).obj (C.projectiveSectionLocalModule base M ij) ≅ P)
    (d : (Scheme.Modules.pullback g).obj (D.projectiveSectionLocalModule base' N kl) ≅ P)
    (a : Γ(T, ⊤)) (ha : IsUnit a)
    (h : SheafOfModules.sectionsMap e.hom
        (pullbackSection f (C.projectiveSectionLocalModule base M ij)
          (isIso_pullbackUnitComparison f) (C.projectiveSectionLocalUniversalSection base M ij)) =
      scaleSection (unitEndomorphismOfRegularFunction a)
        (SheafOfModules.sectionsMap d.hom
          (pullbackSection g (D.projectiveSectionLocalModule base' N kl)
            (isIso_pullbackUnitComparison g)
            (D.projectiveSectionLocalUniversalSection base' N kl)))) :
    (C.projectiveSectionLocalZeroGluedToAmbient base M).ker.comap
        (f ≫ (C.projectiveSectionOpenCover base M).f ij) =
      (D.projectiveSectionLocalZeroGluedToAmbient base' N).ker.comap
        (g ≫ (D.projectiveSectionOpenCover base' N).f kl) := by
  exact serreActualUniversalZero_comap_chart_eq_of_section_unit_scale
    base M base' N C D ij kl f g (e ≪≫ d.symm) a ha
    (serreActualSection_commonModule_unit_scale e d _ _ a h)

end PfaffianDescent
