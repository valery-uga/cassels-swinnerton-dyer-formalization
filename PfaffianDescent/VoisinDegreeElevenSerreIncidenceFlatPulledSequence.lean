import PfaffianDescent.CubicPointTraceFieldBaseChangeFlatPullback
import PfaffianDescent.SerreExtensionFoundation

/-! # Actual flat pullback of the Serre short exact sequence -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

def serreIncidenceFlatPulledSequence
    {X Y : Scheme.{u}} (f : Y ⟶ X) [Flat f] {N : X.Modules}
    (e : SerreExtensionData X N) :
    SerreExtensionSequenceData Y ((Scheme.Modules.pullback f).obj N) := by
  let F := Scheme.Modules.pullback f
  letI : F.Additive := inferInstanceAs ((Scheme.Modules.pullback f).Additive)
  letI : PreservesFiniteLimits F := inferInstanceAs (PreservesFiniteLimits (Scheme.Modules.pullback f))
  letI : PreservesFiniteColimits F := inferInstanceAs (PreservesFiniteColimits (Scheme.Modules.pullback f))
  letI := isIso_pullbackUnitComparison f
  let u := asIso (pullbackUnitComparison f)
  let a := u.inv ≫ F.map e.inclusion
  let b := F.map e.projection
  have hz : a ≫ b = 0 := by
    dsimp [a,b]
    rw [Category.assoc, ← F.map_comp, e.zero, F.map_zero, comp_zero]
  let T := ShortComplex.mk a b hz
  have hS := e.shortExact.map_of_exact F
  let q : (ShortComplex.mk e.inclusion e.projection e.zero).map F ≅ T :=
    ShortComplex.isoMk u (Iso.refl _) (Iso.refl _)
      (by dsimp [T,a]; simp only [Category.assoc, Iso.hom_inv_id_assoc, Category.comp_id]; rfl)
      (by simp [T,b])
  exact { E := F.obj (show X.Modules from e.E)
          inclusion := a
          projection := b
          zero := hz
          shortExact := ShortComplex.shortExact_of_iso q hS }

end PfaffianDescent
