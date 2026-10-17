import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveTwistCoordinate
import PfaffianDescent.BundleSectionZeroLocusNaturality

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreSurfaceJetCotangent_restrictUnit_one
    {X : Scheme.{u}} (U : X.Opens) :
    ((Scheme.Modules.restrictUnitIso U.ι).inv.val.app (op ⊤))
      (1 : Γ((U : Scheme), ⊤)) =
    (schemeModuleRestrictTopSectionIso U
      (SheafOfModules.unit X.ringCatSheaf)).inv (1 : Γ(X, U)) := by
  change (U.ι.appIso ⊤).inv (1 : Γ((U : Scheme), ⊤)) = _
  simp only [map_one]
  unfold schemeModuleRestrictTopSectionIso
  change 1 = (X.presheaf.map (eqToIso U.ι_image_top.symm).op.inv).hom 1
  simp

theorem cubicClosedPointSerreSurfaceJetCotangent_restrictUnit_topCoordinate
    {X : Scheme.{u}} (U : X.Opens) (z : Γ((U : Scheme), ⊤)) :
    (U.topIso.inv).hom
      ((schemeModuleRestrictTopSectionIso U
        (SheafOfModules.unit X.ringCatSheaf)).hom
        (((Scheme.Modules.restrictUnitIso U.ι).inv.val.app (op ⊤)) z)) = z := by
  unfold schemeModuleRestrictTopSectionIso
  simp only [Iso.trans_hom, Functor.mapIso_hom, ConcreteCategory.comp_apply]
  change (U.topIso.inv).hom ((U.topIso.hom).hom ((U.ι.appIso ⊤).inv z)) = z
  rw [Scheme.Opens.ι_appIso]
  exact Iso.hom_inv_id_apply U.topIso z

theorem cubicClosedPointSerreSurfaceJetCotangent_sectionChartCoefficient
    {X : Scheme.{u}} (U : X.Opens) (M : X.Modules)
    (p : (Scheme.Modules.restrictFunctor U.ι).obj M ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf)
    (s : M.sections) :
    BundleSectionZeroLocus.unitEndomorphismValue
      ((Scheme.Modules.restrictUnitIso U.ι).inv ≫
        (Scheme.Modules.restrictFunctor U.ι).map (M.unitHomEquiv.symm s) ≫ p.hom) =
    (U.topIso.inv).hom
      (schemeModuleLocalUnitSectionAddEquiv U M p (s.val (op U))) := by
  let R := Scheme.Modules.restrictFunctor U.ι
  let a := M.unitHomEquiv.symm s
  have ha : a.val.app (op U) (1 : Γ(X, U)) = s.val (op U) := by
    have h := congrArg (fun z => z.val (op U)) (M.unitHomEquiv.apply_symm_apply s)
    simpa only [SheafOfModules.unitHomEquiv_apply_coe] using h
  have hR : ((R.map a).val.app (op ⊤))
      (((Scheme.Modules.restrictUnitIso U.ι).inv.val.app (op ⊤))
        (1 : Γ((U : Scheme), ⊤))) =
      (schemeModuleRestrictTopSectionIso U M).inv (s.val (op U)) := by
    rw [cubicClosedPointSerreSurfaceJetCotangent_restrictUnit_one]
    apply (schemeModuleRestrictTopSectionIso U M).addCommGroupIsoToAddEquiv.injective
    exact (cubicClosedPointSerreSurfaceJetCotangent_restrictTopSectionIso_map U a
      (1 : Γ(X, U))).trans (ha.trans
        (Iso.inv_hom_id_apply (schemeModuleRestrictTopSectionIso U M) (s.val (op U))).symm)
  unfold BundleSectionZeroLocus.unitEndomorphismValue BundleSectionZeroLocus.unitSectionAtTop
  change (p.hom.val.app (op ⊤))
    (((R.map a).val.app (op ⊤))
      (((Scheme.Modules.restrictUnitIso U.ι).inv.val.app (op ⊤))
        (1 : Γ((U : Scheme), ⊤)))) = _
  rw [hR]
  unfold schemeModuleLocalUnitSectionAddEquiv schemeModuleLocalSectionAddEquiv
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_inv, Iso.symm_hom,
    Functor.mapIso_hom, ConcreteCategory.comp_apply]
  change _ = (U.topIso.inv).hom
    ((schemeModuleRestrictTopSectionIso U (SheafOfModules.unit X.ringCatSheaf)).hom
      (((Scheme.Modules.restrictUnitIso U.ι).inv.val.app (op ⊤))
        ((p.hom.val.app (op ⊤))
          ((schemeModuleRestrictTopSectionIso U M).inv (s.val (op U))))))
  exact (cubicClosedPointSerreSurfaceJetCotangent_restrictUnit_topCoordinate U
    ((p.hom.val.app (op ⊤))
      ((schemeModuleRestrictTopSectionIso U M).inv (s.val (op U))))).symm

end PfaffianDescent
