import PfaffianDescent.ActualFieldPointPositiveTwistUnitIso
import PfaffianDescent.SmoothCubicOriginalPointDifferentialFiberDimension

/- SOURCE ONLY / UNVERIFIED. Genuine Omega tensor actual O(2), actual q,
actual pullback, and actual fiber; untwisting and dimension are DERIVED. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev actualCubicPositiveTwoDifferentials
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :=
  schemeModuleTensor (schemeRelativeDifferentials (hypersurfaceToBase p hp))
    (positiveSheafOfModules (grading (equationIdeal p hp)) 2)

def actualCubicPositiveTwoDifferentialPointFiberEquiv
    {K L : Type u} [Field K] [Field L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (q : Spec (CommRingCat.of L) ⟶ hypersurface p hp) :
    (moduleSpecΓFunctor (R := CommRingCat.of L)).obj
      ((Scheme.Modules.pullback q).obj (actualCubicPositiveTwoDifferentials p hp)) ≃ₗ[L]
    (moduleSpecΓFunctor (R := CommRingCat.of L)).obj
      ((Scheme.Modules.pullback q).obj
        (schemeRelativeDifferentials (hypersurfaceToBase p hp))) :=
  ((moduleSpecΓFunctor (R := CommRingCat.of L)).mapIso
    (actualFieldPointPositiveTwistTensorUntwistIso (equationIdeal p hp) q
      (schemeRelativeDifferentials (hypersurfaceToBase p hp)) 2)).toLinearEquiv

/-- Actual Omega(2) has dimension two at SAME original q on a smooth cubic.
All trivialization and tensor comparison facts are internally derived. -/
theorem smoothCubic_originalPositiveTwoDifferentialFiber_finrank_two
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (q : Spec (CommRingCat.of L) ⟶ hypersurface p hp)
    (hq : q ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    Module.finrank L ((moduleSpecΓFunctor (R := CommRingCat.of L)).obj
      ((Scheme.Modules.pullback q).obj (actualCubicPositiveTwoDifferentials p hp))) = 2 := by
  rw [(actualCubicPositiveTwoDifferentialPointFiberEquiv p hp q).finrank_eq]
  exact smoothCubic_originalPointDifferentialFiber_finrank_two p hp hp0 q hq

/-- Actual surjective quotients correspond under the DERIVED untwisting.
The arbitrary quotient is retained; no special trace-selected line is used. -/
lemma actualCubicPositiveTwoDifferentialLine_surjective_iff
    {K L : Type u} [Field K] [Field L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (q : Spec (CommRingCat.of L) ⟶ hypersurface p hp)
    (ell : (moduleSpecΓFunctor (R := CommRingCat.of L)).obj
      ((Scheme.Modules.pullback q).obj (actualCubicPositiveTwoDifferentials p hp)) →ₗ[L] L) :
    Function.Surjective (ell.comp
      (actualCubicPositiveTwoDifferentialPointFiberEquiv p hp q).symm.toLinearMap) ↔
        Function.Surjective ell := by
  constructor
  · intro h c
    obtain ⟨x, hx⟩ := h c
    exact ⟨(actualCubicPositiveTwoDifferentialPointFiberEquiv p hp q).symm x, hx⟩
  · intro h
    exact h.comp (actualCubicPositiveTwoDifferentialPointFiberEquiv p hp q).symm.surjective

end PfaffianDescent
