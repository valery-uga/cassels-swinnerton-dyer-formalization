import PfaffianDescent.CorayProjectiveIntersectionChartDimension
import PfaffianDescent.VoisinDegreeEightFixedCurveScheme
import PfaffianDescent.VoisinCubicSurfaceVanishing
import PfaffianDescent.ClosedImmersionCohomologyOneLinearInjection
import PfaffianDescent.CorayHypersurfaceTwistAmbientFiniteCohomology

/-!
# The OWN component H1 injects into its OWN cubic-ideal H2

All coefficient actions are independently induced by the original base maps.
The actual cubic vanishing, ideal sequence and two genuine maps are internal.
No finite-dimensionality, desired genus/Euler bound, Cartier data, or
pushforward cohomology isomorphism is a hypothesis or asserted conclusion.
SOURCE ONLY / UNVERIFIED; root owns all compiler and audit checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Actual selected-component H1 over ORIGINAL K embeds into H2 of its
literal ideal on the original smooth cubic. No cohomology bound is an input.
Whole p/q integrality is not required. The construction remains independent
of the pending local-principal/Cartier leaves. -/
theorem selectedProjectiveMinimalComponent_ownH1_to_cubicIdealH2_linearInjection
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    [hExtC : HasExt.{u} (scheme C).Modules]
    [hExtY : HasExt.{u} (hypersurface p hp).Modules]
    [hExtAmbient : HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules] :
    let hCp : p ∈ C.toIdeal := hCmin.le (by
      rw [projectiveIntersectionIdeal_toIdeal]
      exact Ideal.subset_span (Set.mem_insert p {q}))
    let i := PfaffianDescent.homogeneousFixedCurveToCubic p hp C hCp
    let L : (hypersurface p hp).Modules := IdealSheafDataModule.closedImmersionModule i
    letI : HasExt.{u} (SheafOfModules.{u} (scheme C).ringCatSheaf) :=
      hExtC
    letI : HasExt.{u} (SheafOfModules.{u} (hypersurface p hp).ringCatSheaf) :=
      hExtY
    letI : Linear K (scheme C).Modules := schemeModulesLinearOver (toBase C)
    letI : Linear K (hypersurface p hp).Modules :=
      schemeModulesLinearOver (hypersurfaceToBase p hp)
    letI : AddCommGroup (schemeModuleCohomology (scheme C)
        (SheafOfModules.unit (scheme C).ringCatSheaf) 1) :=
      @Ext.instAddCommGroup (scheme C).Modules
        (inferInstance : Category (scheme C).Modules)
        (inferInstance : Abelian (scheme C).Modules) hExtC
        (show (scheme C).Modules from SheafOfModules.unit (scheme C).ringCatSheaf) (show (scheme C).Modules from SheafOfModules.unit (scheme C).ringCatSheaf) 1
    letI : AddCommGroup (schemeModuleCohomology (hypersurface p hp) L 2) :=
      @Ext.instAddCommGroup (hypersurface p hp).Modules
        (inferInstance : Category (hypersurface p hp).Modules)
        (inferInstance : Abelian (hypersurface p hp).Modules) hExtY
        (show (hypersurface p hp).Modules from SheafOfModules.unit (hypersurface p hp).ringCatSheaf) (show (hypersurface p hp).Modules from L) 2
    letI : Module K (schemeModuleCohomology (scheme C)
        (show (scheme C).Modules from SheafOfModules.unit (scheme C).ringCatSheaf) 1) :=
      @Ext.instModule K (inferInstance : Ring K) (scheme C).Modules
        (inferInstance : Category (scheme C).Modules)
        (inferInstance : Abelian (scheme C).Modules)
        (schemeModulesLinearOver (toBase C)) hExtC
        (show (scheme C).Modules from SheafOfModules.unit (scheme C).ringCatSheaf) (show (scheme C).Modules from SheafOfModules.unit (scheme C).ringCatSheaf) 1
    letI : Module K (schemeModuleCohomology (hypersurface p hp)
        (show (hypersurface p hp).Modules from L) 2) :=
      @Ext.instModule K (inferInstance : Ring K) (hypersurface p hp).Modules
        (inferInstance : Category (hypersurface p hp).Modules)
        (inferInstance : Abelian (hypersurface p hp).Modules)
        (schemeModulesLinearOver (hypersurfaceToBase p hp)) hExtY
        (show (hypersurface p hp).Modules from SheafOfModules.unit (hypersurface p hp).ringCatSheaf) (show (hypersurface p hp).Modules from L) 2
    ∃ T : schemeModuleCohomology (scheme C)
        (SheafOfModules.unit (scheme C).ringCatSheaf) 1 →ₗ[K]
      schemeModuleCohomology (hypersurface p hp) L 2,
      Function.Injective T := by
  let hCp : p ∈ C.toIdeal := hCmin.le (by
    rw [projectiveIntersectionIdeal_toIdeal]
    exact Ideal.subset_span (Set.mem_insert p {q}))
  let i := PfaffianDescent.homogeneousFixedCurveToCubic p hp C hCp
  let Y := hypersurface p hp
  let pi := hypersurfaceToBase p hp
  let L : (hypersurface p hp).Modules := IdealSheafDataModule.closedImmersionModule i
  letI : IsClosedImmersion i :=
    PfaffianDescent.homogeneousFixedCurveToCubic_closedImmersion p hp C hCp
  letI : HasExt.{u} (SheafOfModules.{u} (scheme C).ringCatSheaf) :=
    hExtC
  letI : HasExt.{u} (SheafOfModules.{u} (hypersurface p hp).ringCatSheaf) :=
    hExtY
  letI : AddCommGroup (schemeModuleCohomology (scheme C)
      (SheafOfModules.unit (scheme C).ringCatSheaf) 1) :=
    @Ext.instAddCommGroup (scheme C).Modules
      (inferInstance : Category (scheme C).Modules)
      (inferInstance : Abelian (scheme C).Modules) hExtC
      (show (scheme C).Modules from SheafOfModules.unit (scheme C).ringCatSheaf) (show (scheme C).Modules from SheafOfModules.unit (scheme C).ringCatSheaf) 1
  letI : AddCommGroup (schemeModuleCohomology (hypersurface p hp) L 2) :=
    @Ext.instAddCommGroup (hypersurface p hp).Modules
      (inferInstance : Category (hypersurface p hp).Modules)
      (inferInstance : Abelian (hypersurface p hp).Modules) hExtY
      (show (hypersurface p hp).Modules from SheafOfModules.unit (hypersurface p hp).ringCatSheaf) (show (hypersurface p hp).Modules from L) 2
  let S := IdealSheafDataModule.closedImmersionModulePushforwardSequence i
  have hS := IdealSheafDataModule.closedImmersionModulePushforwardSequence_shortExact i
  let P : (scheme C ⟶ Spec (CommRingCat.of K)) → Prop := fun rho =>
    letI : Linear K (scheme C).Modules := schemeModulesLinearOver rho
    letI : Linear K Y.Modules := schemeModulesLinearOver pi
    letI : Module K (schemeModuleCohomology (scheme C)
        (show (scheme C).Modules from SheafOfModules.unit (scheme C).ringCatSheaf) 1) :=
      @Ext.instModule K (inferInstance : Ring K) (scheme C).Modules
        (inferInstance : Category (scheme C).Modules)
        (inferInstance : Abelian (scheme C).Modules)
        (schemeModulesLinearOver rho) hExtC
        (show (scheme C).Modules from SheafOfModules.unit (scheme C).ringCatSheaf) (show (scheme C).Modules from SheafOfModules.unit (scheme C).ringCatSheaf) 1
    letI : Module K (schemeModuleCohomology Y
        (show Y.Modules from L) 2) :=
      @Ext.instModule K (inferInstance : Ring K) Y.Modules
        (inferInstance : Category Y.Modules)
        (inferInstance : Abelian Y.Modules)
        (schemeModulesLinearOver pi) hExtY
        (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf) (show Y.Modules from L) 2
    ∃ T : schemeModuleCohomology (scheme C)
        (SheafOfModules.unit (scheme C).ringCatSheaf) 1 →ₗ[K]
      schemeModuleCohomology Y L 2, Function.Injective T
  have hP : P (i ≫ pi) := by
    letI : Linear K (scheme C).Modules := schemeModulesLinearOver (i ≫ pi)
    letI : Linear K Y.Modules := schemeModulesLinearOver pi
    letI : Module K (schemeModuleCohomology (scheme C)
        (show (scheme C).Modules from SheafOfModules.unit (scheme C).ringCatSheaf) 1) :=
      @Ext.instModule K (inferInstance : Ring K) (scheme C).Modules
        (inferInstance : Category (scheme C).Modules)
        (inferInstance : Abelian (scheme C).Modules)
        (schemeModulesLinearOver (i ≫ pi)) hExtC
        (show (scheme C).Modules from SheafOfModules.unit (scheme C).ringCatSheaf) (show (scheme C).Modules from SheafOfModules.unit (scheme C).ringCatSheaf) 1
    letI : Module K (schemeModuleCohomology Y
        (show Y.Modules from L) 2) :=
      @Ext.instModule K (inferInstance : Ring K) Y.Modules
        (inferInstance : Category Y.Modules)
        (inferInstance : Abelian Y.Modules)
        (schemeModulesLinearOver pi) hExtY
        (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf) (show Y.Modules from L) 2
    letI : Subsingleton (schemeModuleCohomology Y S.X₂ 1) :=
      ProjectiveNegativeTwist.cubicSurface_structure_cohomology_one_of_smooth K p hp hp0
    let a := closedImmersion_cohomologyOneLinearMap pi i
      (SheafOfModules.unit (scheme C).ringCatSheaf)
    let b := schemeModuleRestrictionConnectingLinearMapOver pi S hS 1
    exact ⟨b.comp a,
      (schemeModuleRestrictionConnectingLinearMapOver_injective pi S hS 1).comp
        (closedImmersion_cohomologyOneLinearMap_injective pi i
          (SheafOfModules.unit (scheme C).ringCatSheaf))⟩
  have hbase : i ≫ pi = toBase C := by
    change schemeQuotientMap (equationIdeal p hp) C
      (equationIdeal_le_homogeneousIdeal_of_mem hp hCp) ≫ toBase (equationIdeal p hp) = toBase C
    exact schemeQuotientMap_toBase (equationIdeal p hp) C
      (equationIdeal_le_homogeneousIdeal_of_mem hp hCp)
  change P (toBase C)
  exact Eq.mp (congrArg P hbase) hP

end PfaffianDescent.Coray
