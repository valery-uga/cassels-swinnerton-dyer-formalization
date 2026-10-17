import PfaffianDescent.CorayNativeLocalizedProjectiveHyperplanePullback
import PfaffianDescent.CorayExplicitProjectiveEvaluationPoint

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
open scoped PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual native chart evaluation followed by the field-localization
map is exactly the existing normalized projective field-point chart map. -/
theorem nativeLocalizedProjectiveChartMap_fieldLift_eq_genericChartMap001
    {K R F : Type u} [CommRing K] [CommRing R] [Field F]
    {σ : Type} [Fintype σ] (f : K →+* R) (x : σ → R) (a : σ)
    (g : R →+* F) (ha : g (x a) ≠ 0) :
    let ell : Localization.Away (x a) →+* F :=
      IsLocalization.Away.lift (x a) (isUnit_iff_ne_zero.mpr ha)
    ell.comp (nativeLocalizedProjectiveChartMap f x a) =
      projectiveEvaluationChartMap (g.comp f) (fun i => g (x i)) a ha := by
  let ell : Localization.Away (x a) →+* F :=
    IsLocalization.Away.lift (x a) (isUnit_iff_ne_zero.mpr ha)
  have hEll : ell.comp (algebraMap R (Localization.Away (x a))) = g :=
    IsLocalization.Away.lift_comp _ _
  have hEllApply (r : R) : ell (algebraMap R (Localization.Away (x a)) r) = g r :=
    RingHom.congr_fun hEll r
  have hData := nativeLocalizedProjectiveChartMap_hyperplane_pullback001 f x a
  have hInverse : ell (IsLocalization.Away.invSelf (x a)) = (g (x a))⁻¹ := by
    apply mul_left_cancel₀ ha
    have h := congrArg ell (IsLocalization.Away.mul_invSelf (x a) (S := Localization.Away (x a)))
    rw [map_mul, map_one] at h
    rw [hEllApply (x a)] at h
    exact h.trans (mul_inv_cancel₀ ha).symm
  apply projectiveChartMap_ext a
  · rw [RingHom.comp_assoc, hData.1, ← RingHom.comp_assoc, hEll]
    exact (projectiveEvaluationChartMap_base (g.comp f) (fun i => g (x i)) a ha).symm
  · intro i
    change ell (nativeLocalizedProjectiveChartMap f x a (chartCoordinate _ a i)) = _
    rw [hData.2.1 i, map_mul, hEllApply (x i), hInverse,
      projectiveEvaluationChartMap_coordinate, div_eq_mul_inv]

end PfaffianDescent.Coray
