import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Sites.CoverLifting

/- SOURCE ONLY / UNVERIFIED. Canonical site cocontinuity is derived from
actual pullbacks of a covering family, not supplied at a geometric caller. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
variable {Y X : Scheme.{u}}

theorem actualOpenImmersionSite_isCocontinuous
    (f : Y ⟶ X) [IsOpenImmersion f] :
    f.opensFunctor.IsCocontinuous
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) := by
  infer_instance

end PfaffianDescent
