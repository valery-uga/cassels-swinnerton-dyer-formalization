import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodFromStalkLift

/-! # Free neighborhoods from the actual two-generator source sequence -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual two-unit Koszul source gives a free neighborhood when its
projection-compatible stalk basis has been constructed. -/
theorem cubicClosedPointSerreFreeNeighborhood_exists_of_biprod_stalk_lift_iso
    {X : Scheme.{u}} {M : X.Modules} (e : SerreExtensionSequenceData X M)
    (d : SheafOfModules.unit X.ringCatSheaf ⟶
      (SheafOfModules.unit X.ringCatSheaf ⊞ SheafOfModules.unit X.ringCatSheaf))
    (q : (SheafOfModules.unit X.ringCatSheaf ⊞
      SheafOfModules.unit X.ringCatSheaf) ⟶ M)
    (hdq : d ≫ q = 0) (hS : (ShortComplex.mk d q hdq).ShortExact)
    (x : X)
    (l : (schemeModuleStalkModuleFunctor X x).obj
        (SheafOfModules.unit X.ringCatSheaf ⊞ SheafOfModules.unit X.ringCatSheaf) ≅
      (schemeModuleStalkModuleFunctor X x).obj e.E)
    (hl : l.hom ≫ (schemeModuleStalkModuleFunctor X x).map e.projection =
      (schemeModuleStalkModuleFunctor X x).map q) :
    ∃ (U : X.Opens), x ∈ U ∧ IsAffineOpen U ∧
      Nonempty (SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift.{u} (Fin 2)) ≅
        e.E.over U) := by
  let b := cubicClosedPointSerreFreeNeighborhoodUnitBiprodIso X
  let d' := d ≫ b.inv
  let q' := b.hom ≫ q
  have hdq' : d' ≫ q' = 0 := by
    simp [d', q', Category.assoc, hdq]
  let S := ShortComplex.mk d q hdq
  let S' := ShortComplex.mk d' q' hdq'
  let a : S ≅ S' := ShortComplex.isoMk (Iso.refl _) b.symm (Iso.refl _)
    (by simp [S, S', d']) (by simp [S, S', q'])
  have hS' : S'.ShortExact := ShortComplex.shortExact_of_iso a hS
  let F := schemeModuleStalkModuleFunctor X x
  let l' := F.mapIso b ≪≫ l
  have hl' : l'.hom ≫ F.map e.projection = F.map q' := by
    change (F.map b.hom ≫ l.hom) ≫ F.map e.projection = F.map (b.hom ≫ q)
    rw [Category.assoc, hl, F.map_comp]
  exact cubicClosedPointSerreFreeNeighborhood_exists_of_stalk_lift_iso
    e d' q' hdq' hS' x l' hl'

/-- A two-generator source and its constructed stalk basis on an actual
chart give an affine free neighborhood in the original scheme. -/
theorem cubicClosedPointSerreFreeNeighborhood_exists_of_local_biprod_stalk_lift_iso
    {X : Scheme.{u}} {M : X.Modules} (e : SerreExtensionSequenceData X M)
    (U : X.Opens)
    (d : SheafOfModules.unit (U : Scheme).ringCatSheaf ⟶
      (SheafOfModules.unit (U : Scheme).ringCatSheaf ⊞
        SheafOfModules.unit (U : Scheme).ringCatSheaf))
    (q : (SheafOfModules.unit (U : Scheme).ringCatSheaf ⊞
      SheafOfModules.unit (U : Scheme).ringCatSheaf) ⟶ M.restrict U.ι)
    (hdq : d ≫ q = 0) (hS : (ShortComplex.mk d q hdq).ShortExact)
    (x : U)
    (l : (schemeModuleStalkModuleFunctor (U : Scheme) x).obj
        (SheafOfModules.unit (U : Scheme).ringCatSheaf ⊞
          SheafOfModules.unit (U : Scheme).ringCatSheaf) ≅
      (schemeModuleStalkModuleFunctor (U : Scheme) x).obj
        ((show X.Modules from e.E).restrict U.ι))
    (hl : l.hom ≫ (schemeModuleStalkModuleFunctor (U : Scheme) x).map
        ((Scheme.Modules.restrictFunctor U.ι).map e.projection) =
      (schemeModuleStalkModuleFunctor (U : Scheme) x).map q) :
    ∃ (W : X.Opens), U.ι x ∈ W ∧ IsAffineOpen W ∧
      Nonempty (SheafOfModules.free (R := X.ringCatSheaf.over W) (ULift.{u} (Fin 2)) ≅
        e.E.over W) := by
  let eU := cubicClosedPointSerreFreeNeighborhoodRestrictExtension e U
  have h := cubicClosedPointSerreFreeNeighborhood_exists_of_biprod_stalk_lift_iso
    eU d q hdq hS x l hl
  exact cubicClosedPointSerreFreeNeighborhood_exists_ambient_of_chart e.E U x h

end PfaffianDescent
