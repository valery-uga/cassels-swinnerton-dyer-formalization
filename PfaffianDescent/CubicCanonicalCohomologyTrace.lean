import PfaffianDescent.P3CanonicalCohomologyTrace
import PfaffianDescent.P3NegativeOneTopVanishing
import PfaffianDescent.VoisinCubicPushforwardCechExtComparison

/-! # Fully internal canonical scalar trace on cubic-surface cohomology -/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry MvPolynomial AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- The actual cubic restriction sequence identifies pushforward H-two of
O(-1) with ambient H-three of O(-4), with both adjacent vanishings proved. -/
noncomputable def cubicPushforwardNegativeOneCohomologyTwoEquivAmbientNegativeFourThree
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [hExt : HasExt.{u} (Proj PS).Modules] :
    schemeModuleCohomology (Proj PS)
        ((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj
          (sheafOfModules (grading (equationIdeal p hp)) 1)) 2 ≃+
      schemeModuleCohomology (Proj PS) (sheafOfModules PS 4) 3 := by
  let S := hypersurfaceTwistRestrictionSequence p hp 1
  have hS : S.ShortExact :=
    hypersurfaceTwistRestrictionSequence_shortExact p hp hp0 1
  letI : Subsingleton
      (schemeModuleCohomology (Proj PS) S.X₂ 2) := by
    dsimp only [S, hypersurfaceTwistRestrictionSequence]
    change Subsingleton (schemeModuleCohomology (Proj PS)
      (sheafOfModules PS 1) 2)
    exact (p3_negativeTwist_cohomology_one_and_two_subsingleton K 1).2
  letI : Subsingleton
      (schemeModuleCohomology (Proj PS) S.X₂ 3) := by
    dsimp only [S, hypersurfaceTwistRestrictionSequence]
    change Subsingleton (schemeModuleCohomology (Proj PS)
      (sheafOfModules PS 1) 3)
    exact p3NegativeOne_cohomology_three_subsingleton K
  let e := extBoundaryAddEquivOfMiddleSubsingleton.{u, u + 1, u}
    (C := (Proj PS).Modules)
    (show (Proj PS).Modules from
      SheafOfModules.unit (Proj PS).ringCatSheaf) S hS 2
  change Ext.{u}
      (show (Proj PS).Modules from
        SheafOfModules.unit (Proj PS).ringCatSheaf)
      ((Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj
        (sheafOfModules (grading (equationIdeal p hp)) 1)) 2 ≃+
    Ext.{u}
      (show (Proj PS).Modules from
        SheafOfModules.unit (Proj PS).ringCatSheaf)
      (sheafOfModules PS 4) 3
  refine
    { toFun := fun x => e x
      invFun := fun y => e.symm y
      left_inv := fun x => e.left_inv x
      right_inv := fun y => e.right_inv y
      map_add' := fun x y => ?_ }
  exact e.map_add x y


/-- The scalar trace on pushforward H-two of the cubic canonical twist,
normalized by the actual ambient Laurent residue. -/
def cubicPushforwardNegativeOneCohomologyTwoTraceEquiv
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj PS).Modules] :
    schemeModuleCohomology (Proj PS) (cubicPushforwardTwist K p hp 1) 2 ≃+ K :=
  (cubicPushforwardNegativeOneCohomologyTwoEquivAmbientNegativeFourThree K p hp hp0).trans
    (p3NegativeFourCohomologyThreeTraceEquiv K)

/-- A scalar trace on the ACTUAL intrinsic surface cohomology, with no
external Serre-duality or trace-normalization premise. -/
def cubicIntrinsicNegativeOneCohomologyTwoTraceEquiv
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules] :
    schemeModuleCohomology (Proj (grading (equationIdeal p hp)))
      (sheafOfModules (grading (equationIdeal p hp)) 1) 2 ≃+ K :=
  (cubicIntrinsicCohomologyTwoEquivPushforward K p hp hp0 1).trans
    (cubicPushforwardNegativeOneCohomologyTwoTraceEquiv K p hp hp0)

end PfaffianDescent.ProjectiveNegativeTwist
