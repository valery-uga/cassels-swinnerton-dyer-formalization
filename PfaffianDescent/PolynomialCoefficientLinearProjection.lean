import PfaffianDescent.PolynomialCoefficientFaithfullyFlat
import Mathlib.LinearAlgebra.Finsupp.Defs

/-! SOURCE ONLY, UNVERIFIED. A coefficientwise E-linear projection of K
polynomials sends an extended E-ideal back into that same original ideal.
This is the key whole-ideal intersection argument for arbitrary extensions. -/
noncomputable section
namespace PfaffianDescent
open MvPolynomial
universe u v
variable {E K : Type u} [Field E] [Field K] [Algebra E K]
variable {J : Type v}

def coefficientPolynomialProjection (f : K →ₗ[E] E) :
    MvPolynomial J K →+ MvPolynomial J E :=
  AddMonoidAlgebra.coeffAddEquiv.symm.toAddMonoidHom.comp
    ((Finsupp.mapRange.addMonoidHom f.toAddMonoidHom).comp
      AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom)

@[simp] theorem coefficientPolynomialProjection_coeff
    (f : K →ₗ[E] E) (p : MvPolynomial J K) (d : J →₀ ℕ) :
    (coefficientPolynomialProjection f p).coeff d = f (p.coeff d) := rfl

theorem coefficientPolynomialProjection_mul_map
    (f : K →ₗ[E] E) (r : MvPolynomial J K) (q : MvPolynomial J E) :
    coefficientPolynomialProjection f
      (r * MvPolynomial.map (algebraMap E K) q) =
      coefficientPolynomialProjection f r * q := by
  classical
  apply MvPolynomial.ext
  intro d
  simp only [coefficientPolynomialProjection_coeff, MvPolynomial.coeff_mul,
    MvPolynomial.coeff_map, map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  change f (r.coeff a.1 * algebraMap E K (q.coeff a.2)) =
    f (r.coeff a.1) * q.coeff a.2
  have hsmul := f.map_smul (q.coeff a.2) (r.coeff a.1)
  simpa only [Algebra.smul_def, smul_eq_mul, Algebra.algebraMap_self_apply, mul_comm] using hsmul

theorem coefficientPolynomialProjection_mem_of_mem_extendedIdeal
    (f : K →ₗ[E] E) (I : Ideal (MvPolynomial J E))
    (q : MvPolynomial J K)
    (hq : q ∈ I.map (MvPolynomial.map (algebraMap E K))) :
    coefficientPolynomialProjection f q ∈ I := by
  classical
  have h : ∀ r : MvPolynomial J K,
      coefficientPolynomialProjection f (r * q) ∈ I := by
    change q ∈ Submodule.span (MvPolynomial J K)
      ((MvPolynomial.map (algebraMap E K)) '' (I : Set (MvPolynomial J E))) at hq
    induction hq using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨Q, hQ, rfl⟩ := hq
      intro r
      rw [coefficientPolynomialProjection_mul_map]
      exact I.mul_mem_left _ hQ
    | zero => intro r; simp
    | add x y hx hy ihx ihy =>
      intro r
      rw [mul_add, map_add]
      exact I.add_mem (ihx r) (ihy r)
    | smul a q hq ih =>
      intro r
      change coefficientPolynomialProjection f (r * (a * q)) ∈ I
      rw [← mul_assoc]
      exact ih (r * a)
  simpa only [one_mul] using h 1

end PfaffianDescent
