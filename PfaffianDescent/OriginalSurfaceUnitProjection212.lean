import PfaffianDescent.OriginalCurveSurfaceSupportedCoordinates210
import PfaffianDescent.CorayAffineSourceSpecTransport
import PfaffianDescent.BundleSectionZeroLocusNaturality

/-! Exact unit/projection identities for the source Iso used by210.
These reuse the existing restriction unit and pushforward composition laws. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma schemeIsoPushforwardUnitIso_unit212
    {X Y : Scheme.{u}} (e : X ≅ Y) :
    closedImmersionUnitToPushforwardUnit e.hom ≫
      (schemeIsoPushforwardUnitIso e).hom = 𝟙 _ := by
  have hi : (schemeIsoPushforwardUnitIso e).inv =
      (Scheme.Modules.restrictAdjunction e.hom).unit.app
        (SheafOfModules.unit Y.ringCatSheaf) ≫
      (Scheme.Modules.pushforward e.hom).map
        (Scheme.Modules.restrictUnitIso e.hom).hom := rfl
  have hq : closedImmersionUnitToPushforwardUnit e.hom =
      (schemeIsoPushforwardUnitIso e).inv :=
    (BundleSectionZeroLocus.unitToPushforwardObjUnit_eq_restrictAdjunction e.hom).trans hi.symm
  rw [hq]
  exact (schemeIsoPushforwardUnitIso e).inv_hom_id

/-- The actual source Iso and actual composition Iso preserve the unit. -/
theorem schemeIsoCompositePushforwardUnit212
    {X Y Z : Scheme.{u}} (e : X ≅ Y) (g : Y ⟶ Z) :
    closedImmersionUnitToPushforwardUnit (e.hom ≫ g) ≫
      ((Scheme.Modules.pushforwardComp e.hom g).app
        (SheafOfModules.unit X.ringCatSheaf)).inv ≫
      (Scheme.Modules.pushforward g).map (schemeIsoPushforwardUnitIso e).hom =
    closedImmersionUnitToPushforwardUnit g := by
  let F := Scheme.Modules.pushforward g
  let c := (Scheme.Modules.pushforwardComp e.hom g).app
    (SheafOfModules.unit X.ringCatSheaf)
  let v := schemeIsoPushforwardUnitIso e
  let qe := closedImmersionUnitToPushforwardUnit e.hom
  let qg := closedImmersionUnitToPushforwardUnit g
  let qcomp := closedImmersionUnitToPushforwardUnit (e.hom ≫ g)
  have hcomp : qcomp = qg ≫ F.map qe ≫ c.hom :=
    Coray.affineSource_unit_comp e.hom g
  have hc : qcomp ≫ c.inv = qg ≫ F.map qe :=
    (c.comp_inv_eq).mpr
      (hcomp.trans (Category.assoc qg (F.map qe) c.hom).symm)
  have hunit : F.map qe ≫ F.map v.hom = 𝟙 _ :=
    (F.map_comp qe v.hom).symm.trans
      ((congrArg (fun h => F.map h) (schemeIsoPushforwardUnitIso_unit212 e)).trans
        (F.map_id _))
  calc
    _ = (qcomp ≫ c.inv) ≫ F.map v.hom :=
      (Category.assoc qcomp c.inv (F.map v.hom)).symm
    _ = (qg ≫ F.map qe) ≫ F.map v.hom :=
      congrArg (fun h => h ≫ F.map v.hom) hc
    _ = qg ≫ (F.map qe ≫ F.map v.hom) :=
      Category.assoc qg (F.map qe) (F.map v.hom)
    _ = qg ≫ 𝟙 _ := congrArg (fun h => qg ≫ h) hunit
    _ = qg := Category.comp_id qg

namespace Coray
open MvPolynomial AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The literal210 unit-to-plane-cokernel coordinate has the actual
homogeneous restriction projection, derived from its existing quotient law. -/
theorem originalCurveSurfaceUnitCokernelIso_unit212
    (p l : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0)
    (X : Scheme.{u}) (e : X ≅ scheme (projectiveIntersectionIdeal p l hp hl)) :
    closedImmersionUnitToPushforwardUnit
        (e.hom ≫ cubicSecondEquationCurveImmersion p l hp 1 hl) ≫
      (originalCurveSurfaceUnitCokernelIso210 p l hp hp0 hl hl0 X e).hom =
    (unitIsoZeroTwist (grading (equationIdeal p hp))).hom ≫
      (homogeneousRestrictionSequence (grading (equationIdeal p hp))
        (cubicSecondEquationHomogeneous p l hp 1 hl) 0).g := by
  let g := cubicSecondEquationCurveImmersion p l hp 1 hl
  let c := cubicSecondEquation_zeroCokernelIsoCurveUnit p l hp hp0 1 hl
    (nonzeroLinearForm_not_mem_cubic_span p l hp hp0 hl hl0)
  let e₂ := unitIsoZeroTwist (grading (equationIdeal p hp))
  change closedImmersionUnitToPushforwardUnit (e.hom ≫ g) ≫
      (((Scheme.Modules.pushforwardComp e.hom g).app
        (SheafOfModules.unit X.ringCatSheaf)).inv ≫
        ((Scheme.Modules.pushforward g).map (schemeIsoPushforwardUnitIso e).hom ≫ c.inv)) = _
  rw [← Category.assoc, ← Category.assoc]
  have hcomp := schemeIsoCompositePushforwardUnit212 e g
  rw [← Category.assoc] at hcomp
  rw [hcomp]
  apply (cancel_mono c.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hπ :
      (homogeneousRestrictionSequence (grading (equationIdeal p hp))
        (cubicSecondEquationHomogeneous p l hp 1 hl) 0).g ≫ c.hom =
        e₂.inv ≫ closedImmersionUnitToPushforwardUnit g :=
    cubicSecondEquation_zeroCokernelIsoCurveUnit_π p l hp hp0 1 hl
      (nonzeroLinearForm_not_mem_cubic_span p l hp hp0 hl hl0)
  exact (e₂.inv_comp_eq).mp hπ.symm

end Coray
end PfaffianDescent
