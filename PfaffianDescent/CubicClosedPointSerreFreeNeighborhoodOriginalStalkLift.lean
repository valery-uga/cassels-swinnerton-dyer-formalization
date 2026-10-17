import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodBiprodStalkLift
import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodStalkIsoTransport

/-! # Affine free neighborhoods from original-ring stalk coordinates -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual global free module restricted to a chart is the actual
two-unit source there. -/
def cubicClosedPointSerreFreeNeighborhoodLocalFreeToBiprodIso
    {X : Scheme.{u}} (U : X.Opens) :
    (show X.Modules from SheafOfModules.free (R := X.ringCatSheaf)
      (ULift.{u} (Fin 2))).restrict U.ι ≅
      (SheafOfModules.unit (U : Scheme).ringCatSheaf ⊞
        SheafOfModules.unit (U : Scheme).ringCatSheaf) := by
  let R := Scheme.Modules.restrictFunctor U.ι
  letI : R.IsLeftAdjoint := by dsimp [R]; infer_instance
  let a := SheafOfModules.mapFreeIso R (ULift.{u} (Fin 2))
    (Scheme.Modules.restrictUnitIso U.ι).symm
  exact a.symm ≪≫ cubicClosedPointSerreFreeNeighborhoodUnitBiprodIso (U : Scheme)

/-- The constructed original-ring stalk basis and actual affine Koszul
source suffice to construct a free affine neighborhood in the original
scheme. All changes of local rings use the actual restriction stalk map. -/
theorem cubicClosedPointSerreFreeNeighborhood_exists_of_original_stalk_lift_iso
    {X : Scheme.{u}} {M : X.Modules} (e : SerreExtensionSequenceData X M)
    (U : X.Opens)
    (d : SheafOfModules.unit (U : Scheme).ringCatSheaf ⟶
      (SheafOfModules.unit (U : Scheme).ringCatSheaf ⊞
        SheafOfModules.unit (U : Scheme).ringCatSheaf))
    (q : (SheafOfModules.unit (U : Scheme).ringCatSheaf ⊞
      SheafOfModules.unit (U : Scheme).ringCatSheaf) ⟶ M.restrict U.ι)
    (hdq : d ≫ q = 0) (hS : (ShortComplex.mk d q hdq).ShortExact)
    (x : U)
    (l : (schemeModuleStalkModuleFunctor X (U.ι x)).obj
        (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2))) ≅
      (schemeModuleStalkModuleFunctor X (U.ι x)).obj e.E)
    (hl : l.hom ≫ (schemeModuleStalkModuleFunctor X (U.ι x)).map e.projection =
      cubicClosedPointSerreFreeNeighborhoodLocalStalkMap U x
        (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2))) M
        ((cubicClosedPointSerreFreeNeighborhoodLocalFreeToBiprodIso U).hom ≫ q)) :
    ∃ (W : X.Opens), U.ι x ∈ W ∧ IsAffineOpen W ∧
      Nonempty (SheafOfModules.free (R := X.ringCatSheaf.over W) (ULift.{u} (Fin 2)) ≅
        e.E.over W) := by
  let P : X.Modules := SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2))
  let s := cubicClosedPointSerreFreeNeighborhoodLocalFreeToBiprodIso U
  let F := schemeModuleStalkModuleFunctor (U : Scheme) x
  let lU := cubicClosedPointSerreFreeNeighborhoodStalkIsoTransport U x P e.E l
  let lP := F.mapIso s.symm ≪≫ lU
  have hU := cubicClosedPointSerreFreeNeighborhoodStalkIsoTransport_projection
    U x P e.E M l e.projection (s.hom ≫ q) hl
  have hP : lP.hom ≫ F.map ((Scheme.Modules.restrictFunctor U.ι).map e.projection) =
      F.map q := by
    change (F.map s.inv ≫ lU.hom) ≫
      F.map ((Scheme.Modules.restrictFunctor U.ι).map e.projection) = F.map q
    rw [Category.assoc, hU, ← F.map_comp]
    simp only [Iso.inv_hom_id_assoc]
  exact cubicClosedPointSerreFreeNeighborhood_exists_of_local_biprod_stalk_lift_iso
    e U d q hdq hS x lP hP

end PfaffianDescent
