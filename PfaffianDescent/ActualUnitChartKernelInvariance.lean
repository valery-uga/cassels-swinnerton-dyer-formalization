import PfaffianDescent.ActualPositiveRestrictionLocalKernel
import PfaffianDescent.BundleSectionZeroLocus

/- SOURCE ONLY / UNVERIFIED. The kernel of the actual closed-immersion
augmentation is independent of the chosen trivialization. The ratio of
trivializations is an actual unit-module automorphism, not a supplied
coordinate-compatibility or ideal/kernel certificate. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits BundleSectionZeroLocus
open IdealSheafDataModule
universe u

lemma actualUnitEndomorphisms_commute {X : Scheme.{u}}
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) : a ≫ b = b ≫ a := by
  calc
    a ≫ b = unitEndomorphismOfRegularFunction (unitEndomorphismValue (a ≫ b)) :=
      (unitEndomorphismOfRegularFunction_value (a ≫ b)).symm
    _ = unitEndomorphismOfRegularFunction (unitEndomorphismValue (b ≫ a)) := by
      rw [unitEndomorphismValue_comp, unitEndomorphismValue_comp, mul_comm]
    _ = b ≫ a := unitEndomorphismOfRegularFunction_value (b ≫ a)

set_option backward.isDefEq.respectTransparency false in
lemma actualRestrictedUnitEndomorphisms_commute
    {X : Scheme.{u}} (U : X.Opens)
    (a b : (Scheme.Modules.restrictFunctor U.ι).obj
      (SheafOfModules.unit X.ringCatSheaf) ⟶
      (Scheme.Modules.restrictFunctor U.ι).obj
        (SheafOfModules.unit X.ringCatSheaf)) : a ≫ b = b ≫ a := by
  let e : (Scheme.Modules.restrictFunctor U.ι).obj
      (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf :=
    Scheme.Modules.restrictUnitIso U.ι
  apply (cancel_epi e.inv).mp
  apply (cancel_mono e.hom).mp
  have h := actualUnitEndomorphisms_commute
    (e.inv ≫ a ≫ e.hom) (e.inv ≫ b ≫ e.hom)
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h

/-- Postcomposing a local scalar coefficient with ANY actual automorphism of
its unit source preserves the kernel of ANY actual module map out of that
unit. In particular, this applies to the nilpotent-sensitive augmentation. -/
lemma actualRestrictedUnitCoordinate_kernel_invariant
    {X : Scheme.{u}} (U : X.Opens)
    {Q : (U : Scheme).Modules}
    (c : (Scheme.Modules.restrictFunctor U.ι).obj
      (SheafOfModules.unit X.ringCatSheaf) ⟶
      (Scheme.Modules.restrictFunctor U.ι).obj
        (SheafOfModules.unit X.ringCatSheaf))
    (a : (Scheme.Modules.restrictFunctor U.ι).obj
      (SheafOfModules.unit X.ringCatSheaf) ≅
      (Scheme.Modules.restrictFunctor U.ι).obj
        (SheafOfModules.unit X.ringCatSheaf))
    (g : (Scheme.Modules.restrictFunctor U.ι).obj
      (SheafOfModules.unit X.ringCatSheaf) ⟶ Q) :
    (c ≫ a.hom) ≫ g = 0 ↔ c ≫ g = 0 := by
  rw [actualRestrictedUnitEndomorphisms_commute U c a.hom, Category.assoc]
  constructor
  · intro h
    apply (cancel_epi a.hom).mp
    simpa only [comp_zero] using h
  · intro h
    rw [h, comp_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The true positive quotient restriction has local zero kernel computed
using ANY actual chart trivialization of its twist. Its tensor-coordinate
choice is eliminated internally by unit-module kernel invariance. -/
theorem actualPositiveRestriction_local_zero_iff_canonical_coordinate
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.Opens) (T : X.Modules)
    (eT : (SheafOfModules.overFunctor X.ringCatSheaf U).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf U)))
    (canonical : (Scheme.Modules.restrictFunctor U.ι).obj T ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ T) :
    (Scheme.Modules.restrictFunctor U.ι).map
        (s ≫ actualPositiveClosedImmersionRestriction i T) = 0 ↔
      ((Scheme.Modules.restrictFunctor U.ι).map s ≫ canonical.hom ≫
        (Scheme.Modules.restrictUnitIso U.ι).inv) ≫
          (Scheme.Modules.restrictFunctor U.ι).map
            (closedImmersionUnitToPushforwardUnit i) = 0 := by
  let R := Scheme.Modules.restrictFunctor U.ι
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let canonical' : R.obj T ≅ R.obj O :=
    canonical ≪≫ (Scheme.Modules.restrictUnitIso U.ι).symm
  let tensor : R.obj T ≅ R.obj O :=
    R.mapIso (schemeModuleTensorUnitLeftIso T).symm ≪≫
      schemeModuleTensorRestrictIsoOfLocalTrivialization U O T eT
  let ratio : R.obj O ≅ R.obj O := canonical'.symm ≪≫ tensor
  let c := R.map s ≫ canonical'.hom
  have hcoord : actualPositiveRestrictionLocalCoordinate U T eT s =
      c ≫ ratio.hom := by
    dsimp only [actualPositiveRestrictionLocalCoordinate, c, ratio, canonical',
      tensor, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Functor.mapIso_hom, Functor.mapIso_inv]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, R, O]
  rw [actualPositiveRestriction_local_zero_iff i U T eT s, hcoord]
  exact actualRestrictedUnitCoordinate_kernel_invariant U c ratio
    (R.map (closedImmersionUnitToPushforwardUnit i))

end PfaffianDescent
