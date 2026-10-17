import PfaffianDescent.CorayOpenModuleBaseChangeCoherence
import PfaffianDescent.SchemeModuleFiberFrameCoherence
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
Actual open pullback frames from the genuine Cartesian pushforward square.
Uniqueness of left adjoints gives the frame and its original unit law; no
base-change/unit/projection-formula certificate is supplied by the caller.
SOURCE ONLY / UNVERIFIED; root owns all compiler and acceptance checks.
-/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual Cartesian composition comparison as a natural Iso. -/
def schemeModuleOpenPushforwardCompositionNatIso
    {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) :
    Scheme.Modules.pushforward (f ⁻¹ᵁ U).ι ⋙ Scheme.Modules.pushforward f ≅
      Scheme.Modules.pushforward (f ∣_ U) ⋙ Scheme.Modules.pushforward U.ι :=
  Scheme.Modules.pushforwardComp (f ⁻¹ᵁ U).ι f ≪≫
    Scheme.Modules.pushforwardCongr (morphismRestrict_ι f U).symm ≪≫
    (Scheme.Modules.pushforwardComp (f ∣_ U) U.ι).symm

/-- Transport the actual composite adjunction along its original right
comparison, then use uniqueness of left adjoints. This constructs a frame
of the same pullback object; it does not replace that object or any action. -/
def schemeModuleOpenPullbackAdjunctionIso
    {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) (T : X.Modules) :
    (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj
        ((Scheme.Modules.pullback f).obj T) ≅
    (Scheme.Modules.pullback (f ∣_ U)).obj
        ((Scheme.Modules.restrictFunctor U.ι).obj T) :=
  (Adjunction.leftAdjointUniq
    (((Scheme.Modules.pullbackPushforwardAdjunction f).comp
        (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι)).ofNatIsoRight
      (schemeModuleOpenPushforwardCompositionNatIso f U))
    ((Scheme.Modules.restrictAdjunction U.ι).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)))).app T

/-- The actual constructed frame satisfies the original composite unit
law, by the installed left-adjoint uniqueness law and naturality. -/
theorem schemeModuleOpenPullbackAdjunctionIso_composite_unit
    {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) (T : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app T ≫
      (Scheme.Modules.pushforward f).map
        ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι).unit.app
          ((Scheme.Modules.pullback f).obj T)) ≫
      (schemeModuleOpenPushforwardCompositionIso f U
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj
          ((Scheme.Modules.pullback f).obj T))).hom ≫
      (Scheme.Modules.pushforward U.ι).map
        ((Scheme.Modules.pushforward (f ∣_ U)).map
          (schemeModuleOpenPullbackAdjunctionIso f U T).hom) =
    (Scheme.Modules.restrictAdjunction U.ι).unit.app T ≫
      (Scheme.Modules.pushforward U.ι).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app
          ((Scheme.Modules.restrictFunctor U.ι).obj T)) := by
  let A := (Scheme.Modules.pullbackPushforwardAdjunction f).comp
    (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι)
  let B := (Scheme.Modules.restrictAdjunction U.ι).comp
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U))
  let c := schemeModuleOpenPushforwardCompositionNatIso f U
  let E := (A.ofNatIsoRight c).leftAdjointUniq B
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app (A.ofNatIsoRight c) B T
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_unit] at h
  have hn := c.hom.naturality (E.hom.app T)
  rw [Category.assoc] at h
  change A.unit.app T ≫ ((Scheme.Modules.pushforward (f ⁻¹ᵁ U).ι ⋙
      Scheme.Modules.pushforward f).map (E.hom.app T)) ≫
      c.hom.app _ = B.unit.app T at h
  rw [hn] at h
  simpa only [A, B, c, E, schemeModuleOpenPullbackAdjunctionIso,
    schemeModuleOpenPushforwardCompositionNatIso,
    schemeModuleOpenPushforwardCompositionIso, Adjunction.comp_unit_app,
    Iso.trans_hom, NatTrans.comp_app, Iso.app_hom, Iso.app_inv, Iso.symm_hom,
    Functor.comp_obj, Functor.id_obj, Functor.comp_map, Category.assoc] using h

/-- The SAME original adjunction unit commutes with actual open base
change and the internally constructed pullback frame. -/
theorem schemeModuleOpenPullbackAdjunctionIso_unit_square
    {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) (T : X.Modules) :
    (Scheme.Modules.restrictFunctor U.ι).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app T) ≫
      (schemeModuleOpenPushforwardBaseChangeIso f U
        ((Scheme.Modules.pullback f).obj T)).hom ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map
        (schemeModuleOpenPullbackAdjunctionIso f U T).hom =
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app
      ((Scheme.Modules.restrictFunctor U.ι).obj T) := by
  let R := Scheme.Modules.restrictFunctor U.ι
  let Q := Scheme.Modules.pushforward U.ι
  let G := Scheme.Modules.pushforward f
  let P := Scheme.Modules.pullback f
  let V := Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι
  let J := Scheme.Modules.pushforward (f ∣_ U)
  let A := Scheme.Modules.restrictAdjunction U.ι
  let a : J.obj (V.obj (P.obj T)) ⟶
      J.obj ((Scheme.Modules.pullback (f ∣_ U)).obj (R.obj T)) :=
    J.map (schemeModuleOpenPullbackAdjunctionIso f U T).hom
  let b : R.obj T ⟶
      J.obj ((Scheme.Modules.pullback (f ∣_ U)).obj (R.obj T)) :=
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app (R.obj T)
  have hn := A.counit.naturality a
  change R.map (Q.map a) ≫
      A.counit.app (J.obj ((Scheme.Modules.pullback (f ∣_ U)).obj (R.obj T))) =
    A.counit.app (J.obj (V.obj (P.obj T))) ≫ a at hn
  have hb := A.counit.naturality b
  change R.map (Q.map b) ≫
      A.counit.app (J.obj ((Scheme.Modules.pullback (f ∣_ U)).obj (R.obj T))) =
    A.counit.app (R.obj T) ≫ b at hb
  have hc := schemeModuleOpenPullbackAdjunctionIso_composite_unit f U T
  have hm := schemeModuleOpenPushforwardBaseChange_mate f U (P.obj T)
  calc
    _ = R.map ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app T ≫
        G.map ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι).unit.app (P.obj T)) ≫
        (schemeModuleOpenPushforwardCompositionIso f U (V.obj (P.obj T))).hom ≫
        Q.map a) ≫
        A.counit.app (J.obj ((Scheme.Modules.pullback (f ∣_ U)).obj (R.obj T))) := by
      rw [hm]
      simp only [R.map_comp, Category.assoc]
      rw [hn] <;> rfl
    _ = R.map (A.unit.app T ≫ Q.map b) ≫
        A.counit.app (J.obj ((Scheme.Modules.pullback (f ∣_ U)).obj (R.obj T))) := by
      rw [hc] <;> rfl
    _ = R.map (A.unit.app T) ≫ A.counit.app (R.obj T) ≫ b := by
      rw [R.map_comp, Category.assoc, hb]
    _ = b := by
      rw [← Category.assoc, A.left_triangle_components T]
      exact Category.id_comp b

/-- Every genuine unit chart gives a frame of the same pulled-back
coefficient on the actual inverse-image open. -/
def schemeModuleOpenAdjunctionUnitFrameIso
    {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) (T : X.Modules)
    (eT : (Scheme.Modules.restrictFunctor U.ι).obj T ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf) :
    (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj
        ((Scheme.Modules.pullback f).obj T) ≅
      SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf := by
  let j := f ∣_ U
  letI : IsIso (BundleSectionZeroLocus.pullbackUnitComparison j) :=
    BundleSectionZeroLocus.isIso_pullbackUnitComparison j
  exact schemeModuleOpenPullbackAdjunctionIso f U T ≪≫
    (Scheme.Modules.pullback j).mapIso eT ≪≫
    asIso (BundleSectionZeroLocus.pullbackUnitComparison j)

/-- The original unit in that actual frame is the literal local structure
restriction. No compatibility certificate is input. -/
theorem schemeModuleOpenAdjunctionUnitFrameIso_unit_square
    {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) (T : X.Modules)
    (eT : (Scheme.Modules.restrictFunctor U.ι).obj T ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf) :
    (Scheme.Modules.restrictFunctor U.ι).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app T) ≫
      (schemeModuleOpenPushforwardBaseChangeIso f U
        ((Scheme.Modules.pullback f).obj T)).hom ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map
        (schemeModuleOpenAdjunctionUnitFrameIso f U T eT).hom =
    eT.hom ≫ IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (f ∣_ U) := by
  let J := Scheme.Modules.pushforward (f ∣_ U)
  let P := Scheme.Modules.pullback (f ∣_ U)
  let A := Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)
  have hn := A.unit.naturality eT.hom
  change eT.hom ≫ A.unit.app (SheafOfModules.unit U.toScheme.ringCatSheaf) =
    A.unit.app ((Scheme.Modules.restrictFunctor U.ι).obj T) ≫
      J.map (P.map eT.hom) at hn
  have hu := schemeModuleOpenPullbackAdjunctionIso_unit_square f U T
  calc
    _ = ((Scheme.Modules.restrictFunctor U.ι).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app T) ≫
        (schemeModuleOpenPushforwardBaseChangeIso f U
          ((Scheme.Modules.pullback f).obj T)).hom ≫
        J.map (schemeModuleOpenPullbackAdjunctionIso f U T).hom) ≫
        J.map (P.map eT.hom) ≫
        J.map (BundleSectionZeroLocus.pullbackUnitComparison (f ∣_ U)) := by
      simp only [schemeModuleOpenAdjunctionUnitFrameIso, Iso.trans_hom,
        Functor.mapIso_hom, asIso_hom, Functor.map_comp, Category.assoc] <;> rfl
    _ = A.unit.app ((Scheme.Modules.restrictFunctor U.ι).obj T) ≫
        J.map (P.map eT.hom) ≫
        J.map (BundleSectionZeroLocus.pullbackUnitComparison (f ∣_ U)) :=
      congrArg (fun b => b ≫ J.map (P.map eT.hom) ≫
        J.map (BundleSectionZeroLocus.pullbackUnitComparison (f ∣_ U))) hu
    _ = (eT.hom ≫ A.unit.app (SheafOfModules.unit U.toScheme.ringCatSheaf)) ≫
        J.map (BundleSectionZeroLocus.pullbackUnitComparison (f ∣_ U)) := by
      rw [← Category.assoc, ← hn] <;> rfl
    _ = _ := by
      rw [Category.assoc, schemeModulePullbackUnitComparison_unit_square]

end PfaffianDescent
end
