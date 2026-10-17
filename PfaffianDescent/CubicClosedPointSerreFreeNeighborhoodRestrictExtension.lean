import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodImage
import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodUnitExtension

/-! # Actual Serre sequences and free neighborhoods on quotient-unit charts -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- Restriction of the actual sequence uses the canonical actual unit
comparison for its source. -/
def cubicClosedPointSerreFreeNeighborhoodRestrictExtension
    {X : Scheme.{u}} {M : X.Modules} (e : SerreExtensionSequenceData X M)
    (U : X.Opens) : SerreExtensionSequenceData (U : Scheme) (M.restrict U.ι) := by
  let R := Scheme.Modules.restrictFunctor U.ι
  letI : R.Additive := { map_add := by intro A B f g; ext V m; rfl }
  letI : R.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive R
  let u := Scheme.Modules.restrictUnitIso U.ι
  let i := u.inv ≫ R.map e.inclusion
  let p := R.map e.projection
  have hip : i ≫ p = 0 := by
    change (u.inv ≫ R.map e.inclusion) ≫ R.map e.projection = 0
    rw [Category.assoc, ← R.map_comp, e.zero, R.map_zero, comp_zero]
  let S := ShortComplex.mk i p hip
  let a : e.complex.map R ≅ S := ShortComplex.isoMk u (Iso.refl _) (Iso.refl _)
    (by simp [S, i]) (by simp [S, p])
  exact ⟨R.obj e.E, i, p, hip, ShortComplex.shortExact_of_iso a
    (ShortComplex.shortExact_map_restrictFunctor U.ι e.complex e.shortExact)⟩

/-- An actual quotient-unit coordinate on a chart gives actual rank-two
affine neighborhoods in the original ambient scheme. -/
theorem cubicClosedPointSerreFreeNeighborhood_exists_of_local_quotient_unit_iso
    {X : Scheme.{u}} {M : X.Modules} (e : SerreExtensionSequenceData X M)
    (U : X.Opens) (x : U)
    (q : M.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf) :
    ∃ (W : X.Opens), U.ι x ∈ W ∧ IsAffineOpen W ∧
      Nonempty (SheafOfModules.free (R := X.ringCatSheaf.over W)
        (ULift.{u} (Fin 2)) ≅ e.E.over W) := by
  let eU := cubicClosedPointSerreFreeNeighborhoodRestrictExtension e U
  have h := cubicClosedPointSerreFreeNeighborhood_exists_of_quotient_unit_iso eU q x
  exact cubicClosedPointSerreFreeNeighborhood_exists_ambient_of_chart e.E U x h

end PfaffianDescent
