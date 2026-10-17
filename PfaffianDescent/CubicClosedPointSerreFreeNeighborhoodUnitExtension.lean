import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodSection
import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodBiprod
import PfaffianDescent.SheafModulePushforwardExact

/-! # Actual rank-two affine neighborhoods of unit-by-unit extensions -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- Every actual extension of the unit module by the unit module has an
actual rank-two free presentation on an affine neighborhood of each point.
The proof constructs a local splitting; it requires no finite-presentation
or quasicoherence property of the middle sheaf. -/
theorem cubicClosedPointSerreFreeNeighborhood_exists_of_unit_extension
    {X : Scheme.{u}}
    (e : SerreExtensionSequenceData X (SheafOfModules.unit X.ringCatSheaf)) (x : X) :
    ∃ (U : X.Opens), x ∈ U ∧ IsAffineOpen U ∧
      Nonempty (SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift.{u} (Fin 2)) ≅
        e.E.over U) := by
  letI : Epi e.projection := e.shortExact.epi_g
  obtain ⟨U, hxU, hU, s, hs⟩ :=
    cubicClosedPointSerreFreeNeighborhood_exists_affine_section
      (show X.Modules from e.E) e.projection x
  let R := Scheme.Modules.restrictFunctor U.ι
  letI : R.Additive := { map_add := by intro A B f g; ext V m; rfl }
  letI : R.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive R
  let v := Scheme.Modules.restrictUnitIso U.ι
  let i := v.inv ≫ R.map e.inclusion
  let p := R.map e.projection ≫ v.hom
  have hip : i ≫ p = 0 := by
    change (v.inv ≫ R.map e.inclusion) ≫ (R.map e.projection ≫ v.hom) = 0
    rw [Category.assoc, ← Category.assoc (R.map e.inclusion), ← R.map_comp, e.zero,
      R.map_zero, CategoryTheory.Limits.zero_comp, CategoryTheory.Limits.comp_zero]
  let S := ShortComplex.mk i p hip
  let b : e.complex.map R ≅ S := ShortComplex.isoMk v (Iso.refl _) v
    (by simp [S, i]) (by simp [S, p])
  have hS : S.ShortExact := ShortComplex.shortExact_of_iso b
    (ShortComplex.shortExact_map_restrictFunctor U.ι e.complex e.shortExact)
  let t : SheafOfModules.free (R := (U : Scheme.{u}).ringCatSheaf) (ULift.{u} (Fin 2)) ≅
      (show X.Modules from e.E).restrict U.ι :=
    cubicClosedPointSerreFreeNeighborhoodSplitIso _ i p hip hS s hs
  let F := (Scheme.Modules.overEquiv U).functor
  let a := BundleSectionZeroLocus.overEquivFreeIso (X := X) U (ULift.{u} (Fin 2))
  let c := (Scheme.Modules.overFunctorEquiv U).app (show X.Modules from e.E)
  refine ⟨U, hxU, hU, ?_⟩
  exact ⟨F.preimageIso (a.symm ≪≫ t ≪≫ c.symm)⟩

/-- The same direct construction applies once the actual quotient sheaf
is explicitly identified with the unit module. -/
theorem cubicClosedPointSerreFreeNeighborhood_exists_of_quotient_unit_iso
    {X : Scheme.{u}} {M : X.Modules} (e : SerreExtensionSequenceData X M)
    (q : M ≅ SheafOfModules.unit X.ringCatSheaf) (x : X) :
    ∃ (U : X.Opens), x ∈ U ∧ IsAffineOpen U ∧
      Nonempty (SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift.{u} (Fin 2)) ≅
        e.E.over U) := by
  let p := e.projection ≫ q.hom
  have hip : e.inclusion ≫ p = 0 := by
    simp only [p, ← Category.assoc, e.zero, CategoryTheory.Limits.zero_comp]
  let S := ShortComplex.mk e.inclusion p hip
  let b : e.complex ≅ S := ShortComplex.isoMk (Iso.refl _) (Iso.refl _) q
    (by simp [S]) (by simp [S, p])
  let e' : SerreExtensionSequenceData X (SheafOfModules.unit X.ringCatSheaf) :=
    ⟨e.E, e.inclusion, p, hip, ShortComplex.shortExact_of_iso b e.shortExact⟩
  exact cubicClosedPointSerreFreeNeighborhood_exists_of_unit_extension e' x

end PfaffianDescent
