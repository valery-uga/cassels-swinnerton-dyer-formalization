import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodFreeLift
import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodLocalStalkIso
import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodFinitePresentation
import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodRestrictExtension

/-! # Actual free neighborhoods from actual finite presentations and stalk lifts -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- An actual rank-two quotient presentation and an actual native,
projection-compatible stalk isomorphism construct an actual free affine
neighborhood of the original middle sheaf. The stalk map is lifted and its
compatibility is proved on the neighborhood. -/
theorem cubicClosedPointSerreFreeNeighborhood_exists_of_stalk_lift_iso
    {X : Scheme.{u}} {M : X.Modules} (e : SerreExtensionSequenceData X M)
    (d : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2)))
    (q : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2)) ⟶ M)
    (hdq : d ≫ q = 0) (hS : (ShortComplex.mk d q hdq).ShortExact)
    (x : X)
    (l : (schemeModuleStalkModuleFunctor X x).obj
        (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2))) ≅
      (schemeModuleStalkModuleFunctor X x).obj e.E)
    (hl : l.hom ≫ (schemeModuleStalkModuleFunctor X x).map e.projection =
      (schemeModuleStalkModuleFunctor X x).map q) :
    ∃ (U : X.Opens), x ∈ U ∧ IsAffineOpen U ∧
      Nonempty (SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift.{u} (Fin 2)) ≅
        e.E.over U) := by
  obtain ⟨U, hxU, hU, v, hv, hvl⟩ :=
    cubicClosedPointSerreFreeNeighborhood_exists_free_lift_of_stalk
      e.E M e.projection q x l.hom hl
  let R := Scheme.Modules.restrictFunctor U.ι
  letI : R.IsLeftAdjoint := by dsimp [R]; infer_instance
  letI : R.Additive := { map_add := by intro A B f g; ext V m; rfl }
  letI : R.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive R
  let u := Scheme.Modules.restrictUnitIso U.ι
  let a := SheafOfModules.mapFreeIso R (ULift.{u} (Fin 2)) u.symm
  let dU := u.inv ≫ R.map d ≫ a.inv
  let qU := a.hom ≫ R.map q
  have hdqU : dU ≫ qU = 0 := by
    change (u.inv ≫ R.map d ≫ a.inv) ≫ (a.hom ≫ R.map q) = 0
    simp only [Category.assoc, Iso.inv_hom_id_assoc, ← R.map_comp, hdq, R.map_zero, comp_zero]
  let S := ShortComplex.mk d q hdq
  let SU := ShortComplex.mk dU qU hdqU
  let b : S.map R ≅ SU := ShortComplex.isoMk u a.symm (Iso.refl _)
    (by simp [S, SU, dU]) (by simp [S, SU, qU])
  have hSU : SU.ShortExact := ShortComplex.shortExact_of_iso b
    (ShortComplex.shortExact_map_restrictFunctor U.ι S hS)
  let eU := cubicClosedPointSerreFreeNeighborhoodRestrictExtension e U
  let vU := a.hom ≫ v
  have hvU : vU ≫ eU.projection = qU := by
    change (a.hom ≫ v) ≫ R.map e.projection = a.hom ≫ R.map q
    rw [Category.assoc, hv]
  let xU : U := ⟨x, hxU⟩
  letI : IsIso (cubicClosedPointSerreFreeNeighborhoodLocalStalkMap U xU _ e.E v) := by
    rw [hvl]
    infer_instance
  letI : IsIso ((schemeModuleStalkModuleFunctor (U : Scheme) xU).map v) :=
    cubicClosedPointSerreFreeNeighborhood_local_stalk_isIso U xU _ e.E v
  letI : IsIso ((schemeModuleStalkModuleFunctor (U : Scheme) xU).map vU) := by
    change IsIso ((schemeModuleStalkModuleFunctor (U : Scheme) xU).map (a.hom ≫ v))
    rw [Functor.map_comp]
    infer_instance
  have h := cubicClosedPointSerreFreeNeighborhood_exists_of_presentation_lift
    eU dU qU hdqU hSU vU hvU xU
  exact cubicClosedPointSerreFreeNeighborhood_exists_ambient_of_chart e.E U xU h

end PfaffianDescent
