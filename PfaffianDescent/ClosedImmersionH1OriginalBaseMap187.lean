import PfaffianDescent.ClosedImmersionCohomologyOneLinearEquiv

/-! Source-only187. Retain the independently supplied source structure map,
using the true immersion square to re-express the existing native map. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory
universe u
variable {K : Type u} [Field K] {X Y : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual native closed-pushforward map, with the independent source
base action. The ordinary geometric square is its only compatibility input. -/
def closedImmersion_cohomologyOneLinearMapOver187
    [HasExt.{u} X.Modules] [HasExt.{u} Y.Modules]
    (piX : X ⟶ Spec (CommRingCat.of K))
    (piY : Y ⟶ Spec (CommRingCat.of K)) (f : X ⟶ Y) [IsClosedImmersion f]
    (hbase : f ≫ piY = piX) (M : X.Modules) :
    letI : Linear K X.Modules := schemeModulesLinearOver piX
    letI : Linear K Y.Modules := schemeModulesLinearOver piY
    schemeModuleCohomology X M 1 →ₗ[K]
      schemeModuleCohomology Y ((Scheme.Modules.pushforward f).obj M) 1 := by
  subst piX
  exact closedImmersion_cohomologyOneLinearMap piY f M

/-- Equality of actual values with the existing canonical map; only scalar
linearity was expressed through the original geometric square. -/
theorem closedImmersion_cohomologyOneLinearMapOver_apply187
    [HasExt.{u} X.Modules] [HasExt.{u} Y.Modules]
    (piX : X ⟶ Spec (CommRingCat.of K))
    (piY : Y ⟶ Spec (CommRingCat.of K)) (f : X ⟶ Y) [IsClosedImmersion f]
    (hbase : f ≫ piY = piX) (M : X.Modules)
    (z : schemeModuleCohomology X M 1) :
    closedImmersion_cohomologyOneLinearMapOver187 piX piY f hbase M z =
      closedImmersion_cohomologyOneLinearMap piY f M z := by
  subst piX
  rfl

/-- Native exact right-adjoint surjectivity, without any assumed comparison
or cohomology certificate. -/
theorem closedImmersion_cohomologyOneLinearMapOver_surjective187
    [HasExt.{u} X.Modules] [HasExt.{u} Y.Modules]
    (piX : X ⟶ Spec (CommRingCat.of K))
    (piY : Y ⟶ Spec (CommRingCat.of K)) (f : X ⟶ Y) [IsClosedImmersion f]
    (hbase : f ≫ piY = piX) (M : X.Modules) :
    Function.Surjective
      (closedImmersion_cohomologyOneLinearMapOver187 piX piY f hbase M) := by
  subst piX
  exact closedImmersion_cohomologyOneLinearMap_surjective piY f M

end PfaffianDescent.Coray
