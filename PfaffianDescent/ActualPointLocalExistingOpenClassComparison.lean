import PfaffianDescent.ActualPointLocalClassTopNormalization

/-! SOURCE ONLY, UNVERIFIED. Identify the genuine local adjunction-unit
class with the existing actual original-point class of an open section. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

lemma actualRestrictUnitTopSectionNormalization
    {X : Scheme.{u}} (U : X.Opens) (M : X.Modules) (z : Γ(M, U)) :
    (M.restrict U.ι).val.map (eqToHom (congrArg op U.ι_preimage_self))
        (((Scheme.Modules.restrictAdjunction U.ι).unit.app M).val.app (op U) z) =
      (schemeModuleRestrictTopSectionIso U M).inv z := by
  apply (schemeModuleRestrictTopSectionIso U M).addCommGroupIsoToAddEquiv.injective
  rw [Iso.inv_hom_id_apply]
  dsimp only [schemeModuleRestrictTopSectionIso, Iso.trans_hom,
    Scheme.Modules.restrictAppIso]
  simp only [ConcreteCategory.comp_apply, Functor.mapIso_hom]
  change M.val.map _ (M.val.map _ (M.val.map _ z)) = z
  simp only [← PresheafOfModules.map_comp_apply]
  have hid : M.val.map (𝟙 (op U)) z = z := congr_fun (M.val.map_id (op U)) z
  convert hid using 1
  congr 1
  exact Subsingleton.elim _ _

lemma actualPointLocalExistingOpenClassComparison
    {K L : Type u} [Field K] [Field L] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of K)) (U : X.Opens)
    (q : Spec (.of L) ⟶ (U : Scheme)) (M : X.Modules) (z : Γ(M, U)) :
    actualPointLocalSectionClass (q ≫ U.ι) M U
        (by rw [Scheme.Hom.comp_preimage, U.ι_preimage_self]; rfl) z =
      actualModuleOpenPointSectionClass g U q M z := by
  let E := cubicClosedPointSerreSurfaceJetCotangent_pointOpenRestrictPullbackIso U.ι q M
  let G := moduleSpecΓFunctor (R := .of L)
  have hForward : G.map E.hom (actualModuleOpenPointSectionClass g U q M z) =
      actualModulePointSectionClass q (M.restrict U.ι)
        (actualOpenSectionUnitHomAddEquiv g U M z) := by
    change G.map E.hom (G.map E.inv _) = _
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, E.inv_hom_id, Functor.map_id]
    rfl
  have hDirect := actualPointLocalOpenRestrictionComparison U.ι q M U
    (by rw [Scheme.Hom.comp_preimage, U.ι_preimage_self]; rfl) z
  rw [actualPointLocalSectionClass_eq_top q (M.restrict U.ι) _ _ U.ι_preimage_self,
    actualRestrictUnitTopSectionNormalization,
    actualPointLocalSectionClass_top_of_section (U.ι ≫ g)] at hDirect
  change G.map E.hom
    (actualPointLocalSectionClass (q ≫ U.ι) M U _ z) =
      actualModulePointSectionClass q (M.restrict U.ι)
        (actualOpenSectionUnitHomAddEquiv g U M z) at hDirect
  have h := congrArg (fun w => G.map E.inv w) (hDirect.trans hForward.symm)
  simpa only [← ModuleCat.comp_apply, ← Functor.map_comp, E.hom_inv_id,
    Functor.map_id, ModuleCat.id_apply] using h

end PfaffianDescent
