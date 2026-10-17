import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodNativeAway
import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodOriginalStalkLift

/-! # The actual Serre bundle and rank-two affine cover -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- Actual rank-two neighborhoods upgrade the original extension sequence
to the Serre datum used by the pencil construction. -/
def cubicClosedPointSerreFreeNeighborhoodDataOfPointwise
    {X : Scheme.{u}} {M : X.Modules} (e : SerreExtensionSequenceData X M)
    (h : ∀ (x : X), ∃ (U : X.Opens), x ∈ U ∧ IsAffineOpen U ∧
      Nonempty (SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift.{u} (Fin 2)) ≅
        e.E.over U)) : SerreExtensionData X M := by
  classical
  let U : X → X.Opens := fun x => Classical.choose (h x)
  have hU (x : X) : x ∈ U x ∧ IsAffineOpen (U x) ∧
      Nonempty (SheafOfModules.free (R := X.ringCatSheaf.over (U x))
        (ULift.{u} (Fin 2)) ≅ e.E.over (U x)) := Classical.choose_spec (h x)
  exact SerreExtensionData.ofSequence e
    (sheaf_isLocallyFree_of_pointwise_free X e.E U (fun x => (hU x).1)
      (fun _ => ULift.{u} (Fin 2)) (fun x => Classical.choice (hU x).2.2))

/-- Upgrading local freeness retains the exact original extension. -/
theorem cubicClosedPointSerreFreeNeighborhoodDataOfPointwise_toSequenceData
    {X : Scheme.{u}} {M : X.Modules} (e : SerreExtensionSequenceData X M)
    (h : ∀ (x : X), ∃ (U : X.Opens), x ∈ U ∧ IsAffineOpen U ∧
      Nonempty (SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift.{u} (Fin 2)) ≅
        e.E.over U)) :
    (cubicClosedPointSerreFreeNeighborhoodDataOfPointwise e h).toSequenceData = e := by
  cases e
  rfl

/-- The same actual pointwise neighborhoods form the rank-two affine cover
of the upgraded original Serre sequence. -/
def cubicClosedPointSerreFreeNeighborhoodCoverOfPointwise
    {X : Scheme.{u}} {M : X.Modules}
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (e : SerreExtensionSequenceData X M)
    (h : ∀ (x : X), ∃ (U : X.Opens), x ∈ U ∧ IsAffineOpen U ∧
      Nonempty (SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift.{u} (Fin 2)) ≅
        e.E.over U)) :
    SerreExtensionData.SerreExtensionRankTwoAffineCover
      (cubicClosedPointSerreFreeNeighborhoodDataOfPointwise e h) := by
  classical
  let U : X → X.Opens := fun x => Classical.choose (h x)
  have hU (x : X) : x ∈ U x ∧ IsAffineOpen (U x) ∧
      Nonempty (SheafOfModules.free (R := X.ringCatSheaf.over (U x))
        (ULift.{u} (Fin 2)) ≅ e.E.over (U x)) := Classical.choose_spec (h x)
  exact SerreExtensionData.SerreExtensionRankTwoAffineCover.ofPointwise
    (cubicClosedPointSerreFreeNeighborhoodDataOfPointwise e h) U (fun x => (hU x).1)
      (fun x => (hU x).2.1) (fun x => Classical.choice (hU x).2.2)

end PfaffianDescent
