import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentChart
import PfaffianDescent.VoisinProjectiveVectorChartMap

/-! Literal normalization of a square-zero surface jet in a common linear chart. -/
noncomputable section
open AlgebraicGeometry MvPolynomial TrivSqZeroExt HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
variable {K R : Type u} [Field K] [CommRing R] [Algebra K R]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Homogeneous scaling also holds in the actual square-zero algebra. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_aeval_mul_homogeneous
    {σ : Type*} (q : MvPolynomial σ K) {d : ℕ} (hq : q.IsHomogeneous d)
    (a : R) (x : σ → R) :
    aeval (fun j => a * x j) q = a ^ d * aeval x q := by
  classical
  induction hq using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq =>
    rw [map_add, map_add, ihp, ihq, mul_add]
  | monomial s r hs =>
    rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial]
    simp only [mul_pow, Finsupp.prod]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    have hs' : (∑ i ∈ s.support, s i) = d := by
      simpa only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply,
        smul_eq_mul, mul_one] using hs
    rw [hs']
    ring

variable (ell : MvPolynomial (Fin 4) K) (J : Fin 4 → CubicSurfaceFirstJet K)

/-- Normalize using the actual unit value ell(J), including its derivative. -/
def cubicClosedPointSerreSurfaceJetCotangent_normalizedJet
    (hunit : IsUnit (aeval J ell)) : Fin 4 → CubicSurfaceFirstJet K :=
  fun j => (↑hunit.unit⁻¹ : CubicSurfaceFirstJet K) * J j

@[simp] theorem cubicClosedPointSerreSurfaceJetCotangent_normalizedJet_ell
    (hell : ell.IsHomogeneous 1) (hunit : IsUnit (aeval J ell)) :
    aeval (cubicClosedPointSerreSurfaceJetCotangent_normalizedJet ell J hunit) ell = 1 := by
  unfold cubicClosedPointSerreSurfaceJetCotangent_normalizedJet
  rw [cubicClosedPointSerreSurfaceJetCotangent_aeval_mul_homogeneous ell hell]
  rw [pow_one]
  exact hunit.val_inv_mul

/-- Literal q/ell^d in the normalized jet algebra. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_normalizedJet_homogeneous
    (hunit : IsUnit (aeval J ell)) (q : MvPolynomial (Fin 4) K)
    {d : ℕ} (hq : q.IsHomogeneous d) :
    aeval (cubicClosedPointSerreSurfaceJetCotangent_normalizedJet ell J hunit) q =
      (↑hunit.unit⁻¹ : CubicSurfaceFirstJet K) ^ d * aeval J q :=
  cubicClosedPointSerreSurfaceJetCotangent_aeval_mul_homogeneous q hq _ J

/-- The actual cubic equation remains zero after normalization. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_normalizedJet_cubic
    (hunit : IsUnit (aeval J ell)) (p : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hzero : aeval J p = 0) :
    aeval (cubicClosedPointSerreSurfaceJetCotangent_normalizedJet ell J hunit) p = 0 := by
  rw [cubicClosedPointSerreSurfaceJetCotangent_normalizedJet_homogeneous ell J hunit p hp,
    hzero, mul_zero]

/-- On an ideal cubic (zero residue), chart normalization scales the actual
first derivative by the inverse cube of the actual linear-form residue. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_normalizedJet_derivative
    (hunit : IsUnit (aeval J ell)) (q : MvPolynomial (Fin 4) K)
    (hq : q.IsHomogeneous 3) (hqzero : (aeval J q).fst = 0) :
    (aeval (cubicClosedPointSerreSurfaceJetCotangent_normalizedJet ell J hunit) q).snd =
      ((↑hunit.unit⁻¹ : CubicSurfaceFirstJet K).fst) ^ 3 • (aeval J q).snd := by
  rw [cubicClosedPointSerreSurfaceJetCotangent_normalizedJet_homogeneous ell J hunit q hq,
    TrivSqZeroExt.snd_mul, hqzero]
  simp

end PfaffianDescent
