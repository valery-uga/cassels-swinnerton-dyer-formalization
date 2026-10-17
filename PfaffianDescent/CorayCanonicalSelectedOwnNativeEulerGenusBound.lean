import PfaffianDescent.CorayCanonicalSelectedOwnHilbertLowerBound
import PfaffianDescent.CoraySelectedOwnNativeEulerHilbertDictionary

/-! SOURCE ONLY. The selected component native Euler lower bound follows
from SAME whole ideal increments and the genuine OWN Hilbert dictionary.
The Euler constant is the full constant-field rank minus native H1 rank. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- Genuine degree=3r branch bound for the OWN structure-sheaf Euler
characteristic. No constants=K, native genus or rank certificate is supplied. -/
theorem selectedProjectiveMinimalComponent_ownUnitNativeEuler_twice_lower_bound001
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal PS)
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (P : scheme C) [HasExt.{u} (scheme C).Modules]
    (r : ℕ) (hdegree : actualCurveCoordinateHilbertDegree C = 3 * r) :
    0 ≤ 2 * ownUnitNativeEuler C + (3 * r * (r - 1) : ℕ) := by
  obtain ⟨j, hj⟩ := projectivePoint_exists_coordinate_notMem C P
  obtain ⟨B, hB⟩ := selectedProjectiveMinimalComponent_eventually_ownGrade_nativeEuler_affine
    p q hp hp0 n hq hnot C hCmin P j hj
  let d := max B (max r 3)
  have hdB : B ≤ d := Nat.le_max_left _ _
  have hdr : r ≤ d := (Nat.le_max_left r 3).trans (Nat.le_max_right B (max r 3))
  have hd3 : 3 ≤ d := (Nat.le_max_right r 3).trans (Nat.le_max_right B (max r 3))
  have hgrade := selectedOriginalWholeCurve_ownGrade_twice_finrank_lower_bound001
    p q hp hp0 n hq hnot C hCmin r d hdegree hdr hd3
  have hgradeZ : (6 : ℤ) * r * d ≤
      2 * (Module.finrank K (grading C d) : ℤ) + (3 * r * (r - 1) : ℕ) := by
    exact_mod_cast hgrade
  have hlinear := hB d hdB
  rw [hdegree] at hlinear
  rw [hlinear] at hgradeZ
  push_cast at hgradeZ ⊢
  nlinarith

/-- Arithmetic genus means 1-χ here, not H1. This exact equivalent form
remains valid when the constants field has larger original-K rank. -/
theorem selectedProjectiveMinimalComponent_ownArithmeticGenus_twice_upper_bound001
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal PS)
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (P : scheme C) [HasExt.{u} (scheme C).Modules]
    (r : ℕ) (hdegree : actualCurveCoordinateHilbertDegree C = 3 * r) :
    2 * (1 - ownUnitNativeEuler C) ≤ 2 + (3 * r * (r - 1) : ℕ) := by
  have h := selectedProjectiveMinimalComponent_ownUnitNativeEuler_twice_lower_bound001
    p q hp hp0 n hq hnot C hCmin P r hdegree
  linarith

end PfaffianDescent.Coray
