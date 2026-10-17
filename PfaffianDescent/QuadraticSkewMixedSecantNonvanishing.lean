import PfaffianDescent.QuadraticSkewSmoothMixedBlocks
/-! SOURCE ONLY / UNVERIFIED. Dehomogenization is injective on the actual
six mixed monomials; nonzero secant coefficients are therefore DERIVED
from original smoothness, even over finite fields. -/
noncomputable section
namespace PfaffianDescent.QuadraticSkewRationality.MixedNonvanishing
open MvPolynomial Module
open MixedNormalForm OriginalBridge ActualSecant QuarticNet
open scoped BigOperators
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k E : Type u} [Field k] [Field E] [Algebra k E]

def SecantPlaneIndex := ULift.{u} (Fin 2)

def secantExponent (ij : Fin 3 × Fin 2) : SecantPlaneIndex →₀ ℕ :=
  Finsupp.single (ULift.up 0) ij.1.val + Finsupp.single (ULift.up 1) ij.2.val

set_option backward.isDefEq.respectTransparency false in
theorem secantExponent_injective : Function.Injective secantExponent := by
  classical
  intro a b h
  change (Finsupp.single (ULift.up (0 : Fin 2)) a.1.val +
      Finsupp.single (ULift.up (1 : Fin 2)) a.2.val : ULift.{_} (Fin 2) →₀ ℕ) =
    Finsupp.single (ULift.up (0 : Fin 2)) b.1.val +
      Finsupp.single (ULift.up (1 : Fin 2)) b.2.val at h
  apply Prod.ext
  · apply Fin.ext
    have h₀ := DFunLike.congr_fun h (ULift.up (0 : Fin 2))
    simpa [Finsupp.add_apply, Finsupp.single_apply] using h₀
  · apply Fin.ext
    have h₁ := DFunLike.congr_fun h (ULift.up (1 : Fin 2))
    simpa [Finsupp.add_apply, Finsupp.single_apply] using h₁

def leftSecantPolynomial (G : MvPolynomial (Fin 4) E) : MvPolynomial SecantPlaneIndex E :=
  ∑ ij : Fin 3 × Fin 2, monomial (secantExponent ij)
    (G.coeff (leftMixedExponent ij.1 ij.2))

def rightSecantPolynomial (G : MvPolynomial (Fin 4) E) : MvPolynomial SecantPlaneIndex E :=
  ∑ ij : Fin 3 × Fin 2, monomial (secantExponent ij)
    (G.coeff (rightMixedExponent ij.1 ij.2))

/-- For the right piece the first polynomial variable denotes z and the
second denotes t; swapping variables gives B(t,z). -/
theorem coeff_leftSecantPolynomial (G : MvPolynomial (Fin 4) E)
    (ij : Fin 3 × Fin 2) :
    (leftSecantPolynomial G).coeff (secantExponent ij) =
      G.coeff (leftMixedExponent ij.1 ij.2) := by
  classical
  simp [leftSecantPolynomial, coeff_sum, coeff_monomial, secantExponent_injective.eq_iff]

theorem coeff_rightSecantPolynomial (G : MvPolynomial (Fin 4) E)
    (ij : Fin 3 × Fin 2) :
    (rightSecantPolynomial G).coeff (secantExponent ij) =
      G.coeff (rightMixedExponent ij.1 ij.2) := by
  classical
  simp [rightSecantPolynomial, coeff_sum, coeff_monomial, secantExponent_injective.eq_iff]

set_option backward.isDefEq.respectTransparency false in
theorem secantExponent_monomial (ij : Fin 3 × Fin 2) (a : E) :
    monomial (secantExponent ij) a =
      C a * X (ULift.up 0) ^ ij.1.val * X (ULift.up 1) ^ ij.2.val := by
  change (monomial (Finsupp.single (ULift.up (0 : Fin 2)) ij.1.val +
      Finsupp.single (ULift.up (1 : Fin 2)) ij.2.val) a :
      MvPolynomial (ULift.{_} (Fin 2)) E) =
    C a * X (ULift.up (0 : Fin 2)) ^ ij.1.val *
      X (ULift.up (1 : Fin 2)) ^ ij.2.val
  rw [monomial_add_single, ← C_mul_X_pow_eq_monomial]

set_option backward.isDefEq.respectTransparency false in
theorem leftSecantPolynomial_eq_secant_left (G : MvPolynomial (Fin 4) E) :
    leftSecantPolynomial G = leftMixedValue (mappedMixedCoefficients C G)
      1 (X (ULift.up 0)) 1 (X (ULift.up 1)) := by
  change (∑ ij : Fin 3 × Fin 2,
    monomial (Finsupp.single (ULift.up (0 : Fin 2)) ij.1.val +
      Finsupp.single (ULift.up (1 : Fin 2)) ij.2.val)
      (G.coeff (leftMixedExponent ij.1 ij.2)) :
      MvPolynomial (ULift.{_} (Fin 2)) E) =
    leftMixedValue (mappedMixedCoefficients
      (C : E →+* MvPolynomial (ULift.{_} (Fin 2)) E) G)
      1 (X (ULift.up (0 : Fin 2))) 1 (X (ULift.up (1 : Fin 2)))
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three,
    Fin.sum_univ_two, monomial_add_single, ← C_mul_X_pow_eq_monomial]
  simp [leftMixedValue, mappedMixedCoefficients, mixedCoefficients] <;> ring

set_option backward.isDefEq.respectTransparency false in
theorem rightSecantPolynomial_eq_secant_right (G : MvPolynomial (Fin 4) E) :
    rightSecantPolynomial G = rightMixedValue (mappedMixedCoefficients C G)
      1 (X (ULift.up 1)) 1 (X (ULift.up 0)) := by
  change (∑ ij : Fin 3 × Fin 2,
    monomial (Finsupp.single (ULift.up (0 : Fin 2)) ij.1.val +
      Finsupp.single (ULift.up (1 : Fin 2)) ij.2.val)
      (G.coeff (rightMixedExponent ij.1 ij.2)) :
      MvPolynomial (ULift.{_} (Fin 2)) E) =
    rightMixedValue (mappedMixedCoefficients
      (C : E →+* MvPolynomial (ULift.{_} (Fin 2)) E) G)
      1 (X (ULift.up (1 : Fin 2))) 1 (X (ULift.up (0 : Fin 2)))
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three,
    Fin.sum_univ_two, monomial_add_single, ← C_mul_X_pow_eq_monomial]
  simp [rightMixedValue, mappedMixedCoefficients, mixedCoefficients] <;> ring

theorem leftSecantPolynomial_ne_zero_of_blockPiece_ne_zero
    (G : MvPolynomial (Fin 4) E) (hG : G.IsHomogeneous 3)
    (hBlock : blockPiece 2 G ≠ 0) : leftSecantPolynomial G ≠ 0 := by
  intro hzero
  have hc (ij : Fin 3 × Fin 2) : G.coeff (leftMixedExponent ij.1 ij.2) = 0 := by
    have h := congrArg (fun p : MvPolynomial SecantPlaneIndex E =>
      p.coeff (secantExponent ij)) hzero
    simpa only [coeff_leftSecantPolynomial, coeff_zero] using h
  apply hBlock
  rw [blockPiece_two_eq_leftMixedPolynomial G hG]
  simp [leftMixedPolynomial, hc]

theorem rightSecantPolynomial_ne_zero_of_blockPiece_ne_zero
    (G : MvPolynomial (Fin 4) E) (hG : G.IsHomogeneous 3)
    (hBlock : blockPiece 1 G ≠ 0) : rightSecantPolynomial G ≠ 0 := by
  intro hzero
  have hc (ij : Fin 3 × Fin 2) : G.coeff (rightMixedExponent ij.1 ij.2) = 0 := by
    have h := congrArg (fun p : MvPolynomial SecantPlaneIndex E =>
      p.coeff (secantExponent ij)) hzero
    simpa only [coeff_rightSecantPolynomial, coeff_zero] using h
  apply hBlock
  rw [blockPiece_one_eq_rightMixedPolynomial G hG]
  simp [rightMixedPolynomial, hc]

/-- The actual original cubic supplies both nonzero coefficient
polynomials, with no separate nonvanishing premise. -/
theorem original_smooth_cubic_secant_polynomials_ne_zero
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3) (hF₀ : F ≠ 0)
    [AlgebraicGeometry.Smooth (AllCharacteristics.HomogeneousProjective.hypersurfaceToBase F hF)]
    (C : Basis (Fin 4) E (Fin 4 → E)) (P : Matrix (Fin 4) (Fin 4) E)
    (hC : matchingEdgeProjectorMatrix C = P)
    (hLines : MvPolynomial.map (algebraMap k E) F ∈ (projectorLineIdeal P).toIdeal ∧
      MvPolynomial.map (algebraMap k E) F ∈ (projectorLineIdeal (1 - P)).toIdeal) :
    let G := linearSubstitution (basisCoordinateMatrix C) (MvPolynomial.map (algebraMap k E) F)
    leftSecantPolynomial G ≠ 0 ∧ rightSecantPolynomial G ≠ 0 := by
  have hBlocks := original_smooth_cubic_paired_blocks_ne_zero F hF hF₀ C P hC hLines
  have hG := linearSubstitution_homogeneous (basisCoordinateMatrix C) (hF.map (algebraMap k E))
  exact ⟨leftSecantPolynomial_ne_zero_of_blockPiece_ne_zero _ hG hBlocks.1,
    rightSecantPolynomial_ne_zero_of_blockPiece_ne_zero _ hG hBlocks.2⟩

end PfaffianDescent.QuadraticSkewRationality.MixedNonvanishing
