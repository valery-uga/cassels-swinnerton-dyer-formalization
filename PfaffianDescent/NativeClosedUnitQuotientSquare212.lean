import PfaffianDescent.OriginalQuotientUnitCoordinate212
import PfaffianDescent.PointCartierNativeStalkPushforwardComparison
import PfaffianDescent.VoisinHypersurfaceCokernel

/-! The ACTUAL native unit quotient square is the ACTUAL scheme stalkMap.
Existing germ/stalk-pushforward formulas supply the proof, not a certificate. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open IdealSheafDataModule Topology
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma nativeStalkPushforwardUnit_stalkMap212
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsInducing f.base) (x : X)
    (r : Y.presheaf.stalk (f x)) :
    let H := schemeModuleStalkModuleFunctor Y (f x)
    let Phi := ModuleCat.restrictScalars (f.stalkMap x).hom
    let eta := pointCartierNativeStalkPushforwardIso f hf x
      (SheafOfModules.unit X.ringCatSheaf)
    ((eta.hom ≫ Phi.map (schemeModuleUnitStalkIso X x).hom).hom)
      ((H.map (closedImmersionUnitToPushforwardUnit f)).hom
        ((schemeModuleUnitStalkIso Y (f x)).inv.hom r)) = f.stalkMap x r := by
  dsimp only
  change (presheafOfModules_unitStalkLinearEquiv X.presheaf x).symm
    (TopCat.Presheaf.stalkPushforward AddCommGrpCat f.base
      (SheafOfModules.unit X.ringCatSheaf).val.presheaf x
        (closedImmersionPushforwardStalkFromRingLinearMap f (f x) r)) = _
  exact closedImmersionPushforwardStalkFromRingLinearMap_comp_stalkPushforward f x r

/-- After the original quotient equivalence, the original native unit
quotient map is the principal quotient projection. -/
theorem nativeClosedUnit_originalQuotient_square212
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] (x : X)
    (t : Y.presheaf.stalk (f x))
    (e : ((Y.presheaf.stalk (f x)) ⧸ Ideal.span {t}) ≃+* X.presheaf.stalk x)
    (hphi : (f.stalkMap x).hom = e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {t}))) :
    let H := schemeModuleStalkModuleFunctor Y (f x)
    let Phi := ModuleCat.restrictScalars (f.stalkMap x).hom
    let eta := pointCartierNativeStalkPushforwardIso f f.isClosedEmbedding.isInducing x
      (SheafOfModules.unit X.ringCatSheaf)
    H.map (closedImmersionUnitToPushforwardUnit f) ≫ eta.hom ≫
      Phi.map (schemeModuleUnitStalkIso X x).hom ≫
        originalQuotientUnitCoordinate212 t e (f.stalkMap x).hom hphi =
      (schemeModuleUnitStalkIso Y (f x)).hom ≫ (pointCartierYonedaCoefficientComplex t).g := by
  dsimp only
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  obtain ⟨r, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (schemeModuleUnitStalkIso Y (f x)).inv).surjective z
  change e.symm (((pointCartierNativeStalkPushforwardIso f
    f.isClosedEmbedding.isInducing x (SheafOfModules.unit X.ringCatSheaf)).hom ≫
      (ModuleCat.restrictScalars (f.stalkMap x).hom).map
        (schemeModuleUnitStalkIso X x).hom).hom
    (((schemeModuleStalkModuleFunctor Y (f x)).map
      (closedImmersionUnitToPushforwardUnit f)).hom
        ((schemeModuleUnitStalkIso Y (f x)).inv.hom r))) = _
  rw [nativeStalkPushforwardUnit_stalkMap212]
  change e.symm (f.stalkMap x r) =
    (pointCartierYonedaCoefficientComplex t).g
      ((schemeModuleUnitStalkIso Y (f x)).hom
        ((schemeModuleUnitStalkIso Y (f x)).inv r))
  rw [ModuleCat.hom_inv_apply]
  change e.symm (f.stalkMap x r) = Ideal.Quotient.mk (Ideal.span {t}) r
  rw [show f.stalkMap x r = e (Ideal.Quotient.mk (Ideal.span {t}) r) from
    DFunLike.congr_fun hphi r, e.symm_apply_apply]

end PfaffianDescent
