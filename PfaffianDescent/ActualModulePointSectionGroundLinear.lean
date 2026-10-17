import PfaffianDescent.ActualModulePointSectionClass
import AllCharacteristics.SpecGlobalSectionEvaluation

/- SOURCE ONLY / UNVERIFIED. Genuine point-section class is linear over
its actual ground map. The scalar identity follows the true Spec/base square. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def actualModulePointSectionClassGroundLinearMap
    {K L : Type u} [Field K] [Field L] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of K)) (q : Spec (.of L) ⟶ X)
    (beta : K →+* L) (hbase : q ≫ g = Spec.map (CommRingCat.ofHom beta))
    (M : X.Modules) :
    let E := (moduleSpecΓFunctor (R := .of L)).obj ((Scheme.Modules.pullback q).obj M)
    letI : Module K E := Module.compHom E beta
    SchemeModuleGlobalSectionsOver g M →ₗ[K] E := by
  dsimp only
  let E := (moduleSpecΓFunctor (R := .of L)).obj ((Scheme.Modules.pullback q).obj M)
  letI : Module K E := Module.compHom E beta
  refine {
    toFun := actualModulePointSectionClass q M
    map_add' := (actualModulePointSectionClass q M).map_add
    map_smul' := ?_ }
  intro c s
  have hc : q.appTop (affineFunctionHom g c) = (Scheme.ΓSpecIso (.of L)).inv (beta c) := by
    change (g.appTop ≫ q.appTop).hom ((Scheme.ΓSpecIso (.of K)).inv.hom c) = _
    rw [← Scheme.Hom.comp_appTop, hbase]
    exact AllCharacteristics.specMap_appTop_globalSectionsIso_apply beta c
  change actualModulePointSectionClass q M
      (unitEndomorphismOfRegularFunction (affineFunctionHom g c) ≫ s) =
    beta c • actualModulePointSectionClass q M s
  have hscalar : (Scheme.ΓSpecIso (.of L)).hom
      (q.appTop (affineFunctionHom g c)) = beta c := by
    rw [hc, Iso.inv_hom_id_apply]
  exact (actualModulePointSectionClass_regularFunction q M (affineFunctionHom g c) s).trans
    (congrArg (fun a : L => a • actualModulePointSectionClass q M s) hscalar)

@[simp] lemma actualModulePointSectionClassGroundLinearMap_apply
    {K L : Type u} [Field K] [Field L] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of K)) (q : Spec (.of L) ⟶ X)
    (beta : K →+* L) (hbase : q ≫ g = Spec.map (CommRingCat.ofHom beta))
    (M : X.Modules) (s : SchemeModuleGlobalSectionsOver g M) :
    let E := (moduleSpecΓFunctor (R := .of L)).obj ((Scheme.Modules.pullback q).obj M)
    letI : Module K E := Module.compHom E beta
    actualModulePointSectionClassGroundLinearMap g q beta hbase M s =
      actualModulePointSectionClass q M s := rfl

end PfaffianDescent
