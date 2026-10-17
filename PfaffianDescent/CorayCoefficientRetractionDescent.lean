import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.RingTheory.Ideal.Span

/-!
# Actual descent of polynomial principal-ideal membership under field extension

A K-linear coefficient retraction of M -> K is constructed by vector-space
splitting of the actual coefficient inclusion. No supplied trace/retraction
certificate and no division by an extension degree is needed.

Its coefficientwise extension commutes with multiplying by every ground
polynomial. Thus an actual extension-field polynomial quotient descends to
an actual ground-field polynomial quotient.

STATUS: UNVERIFIED source only. Root owns compiler checks.
-/

noncomputable section
namespace PfaffianDescent.Coray

open MvPolynomial

universe u v w
variable {K : Type u} {M : Type v} {σ : Type w}
variable [Field K] [Field M] [Algebra K M]

/-- Actual vector-space splitting constructs a coefficient retraction. -/
theorem fieldCoefficientRetraction_exists :
    ∃ g : M →ₗ[K] K, ∀ a : K, g (algebraMap K M a) = a := by
  have hinj : LinearMap.ker (Algebra.linearMap K M) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (algebraMap K M).injective
  obtain ⟨g, hg⟩ := (Algebra.linearMap K M).exists_leftInverse_of_injective hinj
  refine ⟨g, fun a => ?_⟩
  exact LinearMap.congr_fun hg a

/-- Actual coefficientwise application of a K-linear coefficient map. -/
def polynomialCoefficientRetraction (g : M →ₗ[K] K) :
    MvPolynomial σ M →ₗ[K] MvPolynomial σ K :=
  (AddMonoidAlgebra.coeffLinearEquiv K (S := K) (M := σ →₀ ℕ)).symm.toLinearMap.comp
    ((Finsupp.mapRange.linearMap g).comp
      (AddMonoidAlgebra.coeffLinearEquiv K (S := M) (M := σ →₀ ℕ)).toLinearMap)

theorem polynomialCoefficientRetraction_coeff
    (g : M →ₗ[K] K) (r : MvPolynomial σ M) (n : σ →₀ ℕ) :
    coeff n (polynomialCoefficientRetraction g r) = g (coeff n r) := by
  rfl

/-- Coefficientwise retraction fixes each actual ground polynomial. -/
theorem polynomialCoefficientRetraction_map
    (g : M →ₗ[K] K) (hg : ∀ a : K, g (algebraMap K M a) = a)
    (p : MvPolynomial σ K) :
    polynomialCoefficientRetraction g (MvPolynomial.map (algebraMap K M) p) = p := by
  ext n
  rw [polynomialCoefficientRetraction_coeff, coeff_map, hg]

/-- Multiplication by an actual ground polynomial commutes with coefficient
retraction, proved on the actual finite coefficient convolution. -/
theorem polynomialCoefficientRetraction_map_mul
    (g : M →ₗ[K] K) (p : MvPolynomial σ K) (r : MvPolynomial σ M) :
    polynomialCoefficientRetraction g (MvPolynomial.map (algebraMap K M) p * r) =
      p * polynomialCoefficientRetraction g r := by
  classical
  ext n
  rw [polynomialCoefficientRetraction_coeff, coeff_mul, map_sum, coeff_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [coeff_map, polynomialCoefficientRetraction_coeff]
  simpa [Algebra.smul_def] using
    g.map_smul (coeff a.1 p) (coeff a.2 r)

/-- Actual polynomial divisibility over a field extension descends. The
coefficient retraction is constructed internally rather than supplied. -/
theorem groundPolynomial_dvd_iff_map_dvd
    (p q : MvPolynomial σ K) :
    p ∣ q ↔ MvPolynomial.map (algebraMap K M) p ∣
      MvPolynomial.map (algebraMap K M) q := by
  constructor
  · exact map_dvd (MvPolynomial.map (algebraMap K M))
  · intro hdiv
    obtain ⟨g, hg⟩ := fieldCoefficientRetraction_exists (K := K) (M := M)
    obtain ⟨r, hr⟩ := hdiv
    refine ⟨polynomialCoefficientRetraction g r, ?_⟩
    calc
      q = polynomialCoefficientRetraction g (MvPolynomial.map (algebraMap K M) q) :=
        (polynomialCoefficientRetraction_map g hg q).symm
      _ = polynomialCoefficientRetraction g (MvPolynomial.map (algebraMap K M) p * r) :=
        congrArg (polynomialCoefficientRetraction g) hr
      _ = p * polynomialCoefficientRetraction g r :=
        polynomialCoefficientRetraction_map_mul g p r

/-- Membership in the actual principal polynomial ideal is reflected by
coefficient extension, not assumed as a geometric certificate. -/
theorem groundPolynomial_mem_span_iff_map_mem_span
    (p q : MvPolynomial σ K) :
    q ∈ Ideal.span ({p} : Set (MvPolynomial σ K)) ↔
      MvPolynomial.map (algebraMap K M) q ∈
        Ideal.span ({MvPolynomial.map (algebraMap K M) p} : Set (MvPolynomial σ M)) := by
  rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  exact groundPolynomial_dvd_iff_map_dvd (M := M) p q

/-- The original selected q remains outside the actual base-changed cubic
ideal for every field extension, including the actual residue extension. -/
theorem groundPolynomial_map_not_mem_span
    (p q : MvPolynomial σ K)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial σ K))) :
    MvPolynomial.map (algebraMap K M) q ∉
      Ideal.span ({MvPolynomial.map (algebraMap K M) p} : Set (MvPolynomial σ M)) := by
  intro hmem
  exact hnot ((groundPolynomial_mem_span_iff_map_mem_span (M := M) p q).mpr hmem)

end PfaffianDescent.Coray
