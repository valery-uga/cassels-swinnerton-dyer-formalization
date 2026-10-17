import PfaffianDescent.VoisinHypersurfaceTwist
import PfaffianDescent.VoisinP3TopCechExtComparison

/-!
# The cubic restriction boundary in degrees two and three

This file instantiates the long exact cohomology sequence of

`0 → O_{P³}(-6) → O_{P³}(-3) → i_* O_S(-3) → 0`

for a cubic surface.  The internally proved vanishings of the two adjacent
cohomology groups of `O(-3)` make its connecting homomorphism an additive
equivalence.  Composing with the explicit top-Cech residue calculation gives
the concrete dual-quadratic target used in Voisin's argument.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent.ProjectiveNegativeTwist

universe u

variable (K : Type u) [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- For a nonzero cubic surface, the connecting homomorphism identifies the
second cohomology of the pushed-forward `O_S(-3)` with ambient
`H³(P³,O(-6))`. -/
noncomputable def cubicPushforwardNegativeThreeCohomologyTwoEquivAmbientNegativeSixThree
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [hExt : HasExt.{u} (Proj PS).Modules] :
    schemeModuleCohomology (Proj PS)
        ((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj
          (sheafOfModules (grading (equationIdeal p hp)) 3)) 2 ≃+
      schemeModuleCohomology (Proj PS) (sheafOfModules PS 6) 3 := by
  let S := hypersurfaceTwistRestrictionSequence p hp 3
  have hS : S.ShortExact :=
    hypersurfaceTwistRestrictionSequence_shortExact p hp hp0 3
  letI : Subsingleton
      (schemeModuleCohomology (Proj PS) S.X₂ 2) := by
    dsimp only [S, hypersurfaceTwistRestrictionSequence]
    change Subsingleton (schemeModuleCohomology (Proj PS)
      (sheafOfModules PS 3) 2)
    exact (p3_negativeTwist_cohomology_one_and_two_subsingleton K 3).2
  letI : Subsingleton
      (schemeModuleCohomology (Proj PS) S.X₂ 3) := by
    dsimp only [S, hypersurfaceTwistRestrictionSequence]
    change Subsingleton (schemeModuleCohomology (Proj PS)
      (sheafOfModules PS 3) 3)
    exact p3NegativeThree_cohomology_three_subsingleton K
  let e := extBoundaryAddEquivOfMiddleSubsingleton.{u, u + 1, u}
    (C := (Proj PS).Modules)
    (show (Proj PS).Modules from
      SheafOfModules.unit (Proj PS).ringCatSheaf) S hS 2
  change Ext.{u}
      (show (Proj PS).Modules from
        SheafOfModules.unit (Proj PS).ringCatSheaf)
      ((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj
        (sheafOfModules (grading (equationIdeal p hp)) 3)) 2 ≃+
    Ext.{u}
      (show (Proj PS).Modules from
        SheafOfModules.unit (Proj PS).ringCatSheaf)
      (sheafOfModules PS 6) 3
  refine
    { toFun := fun x => e x
      invFun := fun y => e.symm y
      left_inv := fun x => e.left_inv x
      right_inv := fun y => e.right_inv y
      map_add' := fun x y => ?_ }
  exact e.map_add x y

/-- The cubic restriction boundary followed by the explicit top-Cech residue
duality identifies ambient `H²(i_*O_S(-3))` with the dual of the ten
quadratic forms in four variables. -/
noncomputable def cubicPushforwardNegativeThreeCohomologyTwoEquivDualQuadratic
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [hExt : HasExt.{u} (Proj PS).Modules] :
    schemeModuleCohomology (Proj PS)
        ((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj
          (sheafOfModules (grading (equationIdeal p hp)) 3)) 2 ≃+
      Module.Dual K (homogeneousSubmodule (Fin 4) K 2) :=
  (cubicPushforwardNegativeThreeCohomologyTwoEquivAmbientNegativeSixThree
    K p hp hp0).trans
      (p3NegativeSixCohomologyThreeDualQuadraticEquiv K)

end PfaffianDescent.ProjectiveNegativeTwist
