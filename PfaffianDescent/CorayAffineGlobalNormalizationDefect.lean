import PfaffianDescent.CorayFiniteTorsionAffineSupport
import PfaffianDescent.CorayFiniteTypeNormalization
import PfaffianDescent.CorayNormalizationDefectFiniteLength
import PfaffianDescent.CoraySmoothNormalizedCurveBridge

/-!
# Actual global affine normalization defect is finite over the ground field

Actual finite normalization follows from actual finite-type characteristic-zero
curve equations. Actual fraction denominators give torsion. The actual
annihilator quotient constructs actual finite ground dimension and finite
module support. Smooth cubic/selected-equation wrappers derive the actual
affine dimension bound. No finite defect/support or genus certificate.

This is GLOBAL AFFINE scope, not yet the glued projective normalization
quotient or its cohomological genus correction. Integral branch only.
STATUS: UNVERIFIED source only. Root owns compiler checks.
-/

noncomputable section
namespace PfaffianDescent.Coray

open AlgebraicGeometry Algebra MvPolynomial IsLocalRing Module
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Actual finite-type characteristic-zero curve-domain normalization has
actual finite GLOBAL AFFINE defect dimension over the original ground field. -/
theorem finiteTypeCurve_normalizationDefect_finite_over_ground
    (K A : Type*) [Field K] [CharZero K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.FiniteType K A] [Ring.DimensionLEOne A] :
    Module.Finite K (localNormalizationDefect A (FractionRing A)) := by
  letI : Module.Finite A (integralClosure A (FractionRing A)) :=
    finiteNormalization_of_finiteType_charZero K A
  letI : Module.Finite A (localNormalizationDefect A (FractionRing A)) := inferInstance
  exact finiteTorsion_finite_over_ground K A (localNormalizationDefect A (FractionRing A))
    (localNormalizationDefect_isTorsion A (FractionRing A))

/-- The actual GLOBAL AFFINE normalization defect is supported at an actual
finite set of prime points of the actual original ground affine curve. -/
theorem finiteTypeCurve_normalizationDefect_support_finite
    (K A : Type*) [Field K] [CharZero K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.FiniteType K A] [Ring.DimensionLEOne A] :
    (Module.support A (localNormalizationDefect A (FractionRing A))).Finite := by
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  letI : Module.Finite A (integralClosure A (FractionRing A)) :=
    finiteNormalization_of_finiteType_charZero K A
  letI : Module.Finite A (localNormalizationDefect A (FractionRing A)) := inferInstance
  exact finiteTorsion_support_finite A (localNormalizationDefect A (FractionRing A))
    (localNormalizationDefect_isTorsion A (FractionRing A))

/-- Actual regular intersection dimension plus primitive integral branch
construct the GLOBAL affine DimensionLEOne class. -/
theorem affineCurve_dimensionLEOne_of_prime
    {K : Type*} [Field K]
    (p q : MvPolynomial (Fin 3) K) (hp : Irreducible p)
    (hq : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 3) K)))
    [hcurve : (affineCurveIdeal p q).IsPrime] : Ring.DimensionLEOne (affineCurveRing p q) := by
  letI : Ring.KrullDimLE 1 (affineCurveRing p q) :=
    Ring.krullDimLE_iff.mpr (affineCurve_ringKrullDim_le_one p q hp hq)
  exact ⟨fun {J} hJzero hJprime => hJprime.isMaximal_of_ne_bot hJzero⟩

/-- The actual integral affine intersection has actual finite GLOBAL AFFINE
normalization defect dimension, with normalization and dimension derived. -/
theorem affineCurve_globalNormalizationDefect_finite_over_ground
    {K : Type*} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 3) K) (hp : Irreducible p)
    (hq : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 3) K)))
    [hcurve : (affineCurveIdeal p q).IsPrime] :
    Module.Finite K (localNormalizationDefect (affineCurveRing p q)
      (FractionRing (affineCurveRing p q))) := by
  letI : Ring.DimensionLEOne (affineCurveRing p q) := affineCurve_dimensionLEOne_of_prime p q hp hq
  exact finiteTypeCurve_normalizationDefect_finite_over_ground K (affineCurveRing p q)

/-- The actual original affine curve's GLOBAL AFFINE normalization defect
support is an actual finite set, with no supplied support certificate. -/
theorem affineCurve_globalNormalizationDefect_support_finite
    {K : Type*} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 3) K) (hp : Irreducible p)
    (hq : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 3) K)))
    [hcurve : (affineCurveIdeal p q).IsPrime] :
    (Module.support (affineCurveRing p q) (localNormalizationDefect (affineCurveRing p q)
      (FractionRing (affineCurveRing p q)))).Finite := by
  letI : Ring.DimensionLEOne (affineCurveRing p q) := affineCurve_dimensionLEOne_of_prime p q hp hq
  exact finiteTypeCurve_normalizationDefect_support_finite K (affineCurveRing p q)

/-- Actual smooth homogeneous ground cubic and selected homogeneous ground
q construct actual finite GLOBAL AFFINE defect over K on its integral branch. -/
theorem groundSelectedCurve_globalAffineNormalizationDefect_finite_over_ground
    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hqhom : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) (anchor : Fin 4)
    [hcurve : (affineCurveIdeal
      (normalizedAffineEquation anchor p) (normalizedAffineEquation anchor q)).IsPrime] :
    Module.Finite K (localNormalizationDefect
      (affineCurveRing (normalizedAffineEquation anchor p) (normalizedAffineEquation anchor q))
      (FractionRing (affineCurveRing
        (normalizedAffineEquation anchor p) (normalizedAffineEquation anchor q)))) :=
  affineCurve_globalNormalizationDefect_finite_over_ground _ _
    (normalizedAffineEquation_irreducible_of_smooth_cubic p hp hp0 anchor)
    (normalizedAffineEquation_not_mem_of_smooth_cubic p q hp hp0 n hqhom hnot anchor)

/-- The actual selected original coordinate-one affine ground curve has
actual finite GLOBAL AFFINE normalization-defect support. No point-field
extension or degree-weight certificate is required for this support theorem. -/
theorem groundSelectedCurve_globalAffineNormalizationDefect_support_finite
    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hqhom : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) (anchor : Fin 4)
    [hcurve : (affineCurveIdeal
      (normalizedAffineEquation anchor p) (normalizedAffineEquation anchor q)).IsPrime] :
    (Module.support
      (affineCurveRing (normalizedAffineEquation anchor p) (normalizedAffineEquation anchor q))
      (localNormalizationDefect
        (affineCurveRing (normalizedAffineEquation anchor p) (normalizedAffineEquation anchor q))
        (FractionRing (affineCurveRing
          (normalizedAffineEquation anchor p) (normalizedAffineEquation anchor q))))).Finite :=
  affineCurve_globalNormalizationDefect_support_finite _ _
    (normalizedAffineEquation_irreducible_of_smooth_cubic p hp hp0 anchor)
    (normalizedAffineEquation_not_mem_of_smooth_cubic p q hp hp0 n hqhom hnot anchor)

end PfaffianDescent.Coray
