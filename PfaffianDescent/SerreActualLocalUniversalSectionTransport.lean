import PfaffianDescent.SerreActualLocalUniversalSectionPullback

/-! Transport a literal local universal section through its actual chart
composition isomorphism and a second module isomorphism. The linear-family
calculation can then be supplied by the native coefficient-bundle theorem. -/
noncomputable section
open AlgebraicGeometry CategoryTheory Module
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreActualLocalUniversalSection_afterModuleIso
    {K : Type u} [Field K] {X T : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {ι : Type u} (C : SchemeModuleFiniteFreeAffineCover M ι)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    (f : T ⟶ (C.projectiveSectionOpenCover base M).X ij)
    (q : T ⟶ X) (h : f ≫ C.projectiveSectionOpenCoverToSurface base M ij = q)
    {P : T.Modules} (d : (Scheme.Modules.pullback q).obj M ≅ P)
    (v : Fin (finrank K (SchemeModuleGlobalSectionsOver base M)) → Γ(T, ⊤))
    (s : P.sections)
    (hcoeff : ∀ i, f.appTop (C.projectiveSectionLocalCoefficient base M ij i) = v i)
    (hfamily : SheafOfModules.sectionsMap d.hom
      (parameterizedSchemeModuleSection base M q v
        (finBasis K (SchemeModuleGlobalSectionsOver base M))) = s) :
    SheafOfModules.sectionsMap
      ((((Scheme.Modules.pullbackComp f
          (C.projectiveSectionOpenCoverToSurface base M ij)).app M ≪≫
        (Scheme.Modules.pullbackCongr h).app M) ≪≫ d).hom)
      (pullbackSection f (C.projectiveSectionLocalModule base M ij)
        (isIso_pullbackUnitComparison f)
        (C.projectiveSectionLocalUniversalSection base M ij)) = s := by
  rw [Iso.trans_hom, SheafOfModules.sectionsMap_comp,
    serreActualLocalUniversalSection_pullbackComp base M C ij f q h]
  have hv : (fun i => f.appTop (C.projectiveSectionLocalCoefficient base M ij i)) = v :=
    funext hcoeff
  rw [hv]
  exact hfamily

end PfaffianDescent
