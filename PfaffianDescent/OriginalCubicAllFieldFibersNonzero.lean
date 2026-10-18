import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
The manuscript's nonzero
closed cubic fibre makes the equation primitive over the local base.
Consequently its equation is nonzero over every field-valued Artin test,
including field extensions of the generic fibre.
-/

noncomputable section
namespace PfaffianDescent
universe u v w t
set_option autoImplicit false

theorem polynomial_exists_unit_coefficient_of_nonzero_residue001
    {R : Type u} [CommRing R] [IsLocalRing R]
    {K : Type v} [Field K] {σ : Type t}
    (b : R →+* K) (hb : Function.Surjective b)
    (q : MvPolynomial σ R) (hq : q.map b ≠ 0) :
    ∃ d, IsUnit (MvPolynomial.coeff d q) := by
  obtain ⟨d, hd⟩ := MvPolynomial.exists_coeff_ne_zero hq
  have hd' : b (MvPolynomial.coeff d q) ≠ 0 := by
    simpa only [MvPolynomial.coeff_map] using hd
  refine ⟨d, IsLocalRing.notMem_maximalIdeal.mp ?_⟩
  rw [← IsLocalRing.ker_eq_maximalIdeal b hb]
  exact hd'

theorem polynomial_map_ne_zero_every_field_of_nonzero_residue001
    {R : Type u} [CommRing R] [IsLocalRing R]
    {K : Type v} [Field K] {L : Type w} [Field L] {σ : Type t}
    (b : R →+* K) (hb : Function.Surjective b)
    (q : MvPolynomial σ R) (hq : q.map b ≠ 0) (c : R →+* L) :
    q.map c ≠ 0 := by
  obtain ⟨d, hd⟩ := polynomial_exists_unit_coefficient_of_nonzero_residue001 b hb q hq
  intro he
  have hz := congrArg (MvPolynomial.coeff d) he
  simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at hz
  exact (hd.map c).ne_zero hz

end PfaffianDescent
end
