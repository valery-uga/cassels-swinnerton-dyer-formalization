import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCubicCoefficientGlobalSectionsIso
import PfaffianDescent.SerreActualPointPulledSections

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist BundleSectionZeroLocus
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem pointSplittingGroundKernel_baseCongr_apply
    {F : Type u} [Field F] {X : Scheme.{u}}
    (b b' : X ⟶ Spec (.of F)) (h : b = b') (M : X.Modules)
    (s : SchemeModuleGlobalSectionsOver b M) :
    serreIncidenceGlobalSectionsBaseCongr b b' h M s = s := by
  subst b'
  rfl

theorem pointSplittingGroundKernel_schemeIso_apply
    {F : Type u} [Field F] {X Y : Scheme.{u}}
    (b : X ⟶ Spec (.of F)) (e : Y ≅ X) (M : X.Modules)
    (s : SchemeModuleGlobalSectionsOver b M) :
    cubicClosedPointSerreDegreeThreeEvaluationSchemeIsoLinearEquiv b e M s =
      serreActualPulledGlobalSection b (e.hom ≫ b) e.hom M s := by
  unfold serreActualPulledGlobalSection
  rw [pullbackSection_unitHomEquiv_symm_eq_inv, Equiv.symm_apply_apply]
  rfl

theorem pointSplittingGroundKernel_moduleIso_apply
    {F : Type u} [Field F] {X : Scheme.{u}}
    (b : X ⟶ Spec (.of F)) {M N : X.Modules} (e : M ≅ N)
    (s : SchemeModuleGlobalSectionsOver b M) :
    cubicClosedPointSerreDegreeThreeEvaluationModuleIsoLinearEquiv b e s = s ≫ e.hom := rfl

def pointSplittingGroundKernel_coefficientModuleIso
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (M : (hypersurface p hp).Modules) :=
  (Scheme.Modules.pullbackComp (hypersurfaceBaseChangeIso (algebraMap K F) p hp).hom
    (schemeFieldBaseChangeToOriginal (L := F) (hypersurfaceToBase p hp))).app M ≪≫
    (Scheme.Modules.pullbackCongr
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap_eq_projection
        (algebraMap K F) p hp)).app M

theorem pointSplittingGroundKernel_coefficientIso_apply
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (M : (hypersurface p hp).Modules)
    (t : SchemeModuleGlobalSectionsOver
      (schemeFieldBaseChangeToField (L := F) (hypersurfaceToBase p hp))
      ((Scheme.Modules.pullback
        (schemeFieldBaseChangeToOriginal (L := F) (hypersurfaceToBase p hp))).obj M)) :
    serreIncidenceCubicCoefficientGlobalSectionsIso (F := F) p hp M t =
      letI := isIso_pullbackUnitComparison (hypersurfaceBaseChangeIso (algebraMap K F) p hp).hom
      (inv (pullbackUnitComparison (hypersurfaceBaseChangeIso (algebraMap K F) p hp).hom) ≫
        (Scheme.Modules.pullback (hypersurfaceBaseChangeIso (algebraMap K F) p hp).hom).map t) ≫
      (pointSplittingGroundKernel_coefficientModuleIso (F := F) p hp M).hom := by
  letI := isIso_pullbackUnitComparison (hypersurfaceBaseChangeIso (algebraMap K F) p hp).hom
  simp only [serreIncidenceCubicCoefficientGlobalSectionsIso,
    LinearEquiv.trans_apply, pointSplittingGroundKernel_baseCongr_apply,
    pointSplittingGroundKernel_moduleIso_apply]
  rw [pointSplittingGroundKernel_schemeIso_apply]
  simp only [serreActualPulledGlobalSection,
    pullbackSection_unitHomEquiv_symm_eq_inv, Equiv.symm_apply_apply]
  rfl

theorem pointSplittingGroundKernel_pulledGlobalSection_comp
    {K F G : Type u} [Field K] [Field F] [Field G]
    {X Y Z : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (baseY : Y ⟶ Spec (.of F)) (baseZ : Z ⟶ Spec (.of G))
    (f : Z ⟶ Y) (g : Y ⟶ X) (q : Z ⟶ X) (h : f ≫ g = q)
    (M : X.Modules) (s : SchemeModuleGlobalSectionsOver base M) :
    (letI := isIso_pullbackUnitComparison f;
      inv (pullbackUnitComparison f) ≫ (Scheme.Modules.pullback f).map
        (serreActualPulledGlobalSection base baseY g M s)) ≫
      ((Scheme.Modules.pullbackComp f g).app M ≪≫
        (Scheme.Modules.pullbackCongr h).app M).hom =
    serreActualPulledGlobalSection base baseZ q M s := by
  have hs := sectionsMap_pullbackComp_pullbackCongr_pullbackSection f g q h M
    (isIso_pullbackUnitComparison _) (isIso_pullbackUnitComparison _)
    (isIso_pullbackUnitComparison _) (isIso_pullbackUnitComparison _) (M.unitHomEquiv s)
  have hm := congrArg (((Scheme.Modules.pullback q).obj M).unitHomEquiv.symm) hs
  erw [← SheafOfModules.unitHomEquiv_symm_comp,
    pullbackSection_unitHomEquiv_symm_eq_inv,
    pullbackSection_unitHomEquiv_symm_eq_inv,
    pullbackSection_unitHomEquiv_symm_eq_inv] at hm
  simpa only [serreActualPulledGlobalSection,
    pullbackSection_unitHomEquiv_symm_eq_inv, Equiv.symm_apply_apply] using hm

/-- The coefficient-cubic Gamma comparison sends a genuinely pulled original
section to its literal pullback along the coefficient map. -/
theorem pointSplittingCubicSerreGroundKernel_coefficientIso_pulled
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (M : (hypersurface p hp).Modules)
    (s : SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) M) :
    serreIncidenceCubicCoefficientGlobalSectionsIso (F := F) p hp M
      (serreActualPulledGlobalSection (hypersurfaceToBase p hp)
        (schemeFieldBaseChangeToField (L := F) (hypersurfaceToBase p hp))
        (schemeFieldBaseChangeToOriginal (L := F) (hypersurfaceToBase p hp)) M s) =
    serreActualPulledGlobalSection (hypersurfaceToBase p hp)
      (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp) M s := by
  rw [pointSplittingGroundKernel_coefficientIso_apply]
  exact pointSplittingGroundKernel_pulledGlobalSection_comp
    (hypersurfaceToBase p hp)
    (schemeFieldBaseChangeToField (L := F) (hypersurfaceToBase p hp))
    (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
    (hypersurfaceBaseChangeIso (algebraMap K F) p hp).hom
    (schemeFieldBaseChangeToOriginal (L := F) (hypersurfaceToBase p hp))
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap_eq_projection (algebraMap K F) p hp) M s

end PfaffianDescent
