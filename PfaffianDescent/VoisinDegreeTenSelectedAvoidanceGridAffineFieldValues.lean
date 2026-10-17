import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridCoordinateValues
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridPulledCoordinates

/-! Literal coefficients and coordinate matrices at the actual affine
fraction-field point, proved independently of the native finite datum. -/
noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_affineFieldPoint_baseCoefficientHom
    {K F : Type u} [Field K] [Field F] {U : Scheme.{u}} [IsAffine U]
    (g : Γ(U, ⊤) →+* F) (t : U ⟶ Spec (.of K))
    (b : K →+* Γ(U, ⊤))
    (hb : b = voisinDegreeTenSelectedAvoidance_affineBaseRingMap U t) :
    g.comp b = (Spec.preimage
      (voisinDegreeTenSelectedAvoidance_affineFieldPoint g ≫ t)).hom := by
  subst b
  ext r
  exact (voisinDegreeTenSelectedAvoidance_affineFieldPoint_coordinate_value g t r).symm

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_affineFieldPoint_pulledCoordinateMatrix
    {K F : Type u} [Field K] [Field F] {U : Scheme.{u}} [IsAffine U]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (n : ℕ)
    (g : Γ(U, ⊤) →+* F)
    (t : Fin n → (U ⟶ Spec (.of (Away (grading I) (coordinate I 0)))))
    (x : Fin n → Fin 4 → Γ(U, ⊤))
    (hx : x = fun k z => pulledLinearChartCoordinate I (coordinate I 0)
      (coordinate_mem I 0) U (t k) z) :
    (fun l k => (Spec.preimage
      (voisinDegreeTenSelectedAvoidance_affineFieldPoint g ≫ t k)).hom
        (linearChartCoordinate I (coordinate I 0) (coordinate_mem I 0) l)) =
      (fun l k => g (x k l)) := by
  funext l k
  have hvalue := voisinDegreeTenSelectedAvoidance_affineFieldPoint_coordinate_value g (t k)
    (linearChartCoordinate I (coordinate I 0) (coordinate_mem I 0) l)
  refine hvalue.trans ?_
  exact congrArg g (congrFun (congrFun hx k) l).symm

end PfaffianDescent
