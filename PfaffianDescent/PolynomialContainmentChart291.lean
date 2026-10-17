import PfaffianDescent.MonomialWholeIdealChartNaturality287

/-! Finite equations for containment in a polynomial hypersurface on a
monomial chart. The equations control the entire ideal, including nilpotents. -/
noncomputable section
namespace PfaffianDescent
open MvPolynomial
open scoped Matrix
universe u
variable {A D : Type u} [CommRing A] [CommRing D] {m n : ℕ}
variable (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n)

/-- The coefficient of the polynomial applied to the cyclic unit vector. -/
def cyclicPolynomialContainmentCoefficient291
    (M : CyclicCommutingMatrixPoint283 m n B k (A := A))
    (p : MvPolynomial (Fin m) A) (a : Fin n) : A :=
  commutingMatrixEvaluation282 M.matrices M.commute p a k

/-- These finitely many equations impose vanishing on the entire quotient. -/
def cyclicPolynomialContainmentIdeal291
    (M : CyclicCommutingMatrixPoint283 m n B k (A := A))
    (p : MvPolynomial (Fin m) A) : Ideal A :=
  Ideal.span (Set.range (cyclicPolynomialContainmentCoefficient291 B k M p))

theorem cyclicPolynomialContainmentIdeal_fg291
    (M : CyclicCommutingMatrixPoint283 m n B k (A := A))
    (p : MvPolynomial (Fin m) A) : (cyclicPolynomialContainmentIdeal291 B k M p).FG :=
  Submodule.fg_span (Set.finite_range _)

theorem cyclicPolynomial_mem_wholeIdeal_iff291
    (M : CyclicCommutingMatrixPoint283 m n B k (A := A))
    (p : MvPolynomial (Fin m) A) :
    p ∈ (cyclicMatrixWholeIdealChart287 B k M).val ↔
      ∀ a, cyclicPolynomialContainmentCoefficient291 B k M p a = 0 := by
  classical
  change commutingMatrixPolynomialAction282 M.matrices M.commute p = 0 ↔ _
  rw [← polynomialCyclicEvaluation_zero_iff281
    (commutingMatrixPolynomialAction282 M.matrices M.commute) (Pi.single k 1) B M.cyclic p]
  simp only [polynomialCyclicEvaluation_apply281, commutingMatrixPolynomialAction_apply282,
    Matrix.mulVec_single_one, funext_iff, Pi.zero_apply,
    cyclicPolynomialContainmentCoefficient291, Matrix.col_apply]

theorem cyclicPolynomialContainmentCoefficient_map291
    (M : CyclicCommutingMatrixPoint283 m n B k (A := A))
    (f : A →+* D) (p : MvPolynomial (Fin m) A) (a : Fin n) :
    cyclicPolynomialContainmentCoefficient291 B k (cyclicMatrixPointMap287 B k f M)
        (MvPolynomial.map f p) a =
      f (cyclicPolynomialContainmentCoefficient291 B k M p a) := by
  exact congrArg (fun T : Matrix (Fin n) (Fin n) D => T a k)
    (commutingMatrixEvaluation_map282 M.matrices M.commute f
      (fun i => (M.matrices i).map f)
      (commutingMatrix_tuple_map_commute285 M.matrices M.commute f) (fun _ => rfl) p)

/-- Vanishing of coefficient equations is exactly containment after any
coefficient ring map; no reducedness or flatness assumption is needed. -/
theorem cyclicPolynomialContainmentIdeal_le_ker_iff291
    (M : CyclicCommutingMatrixPoint283 m n B k (A := A))
    (f : A →+* D) (p : MvPolynomial (Fin m) A) :
    cyclicPolynomialContainmentIdeal291 B k M p ≤ RingHom.ker f ↔
      MvPolynomial.map f p ∈
        (cyclicMatrixWholeIdealChart287 B k (cyclicMatrixPointMap287 B k f M)).val := by
  rw [cyclicPolynomial_mem_wholeIdeal_iff291]
  constructor
  · intro h a
    rw [cyclicPolynomialContainmentCoefficient_map291]
    exact h (Ideal.subset_span (Set.mem_range_self a))
  · intro h
    apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact (cyclicPolynomialContainmentCoefficient_map291 B k M f p a).symm.trans (h a)

/-- Specialization of the finite equations classifies containment in the
literal mapped ideal of the original chart point. -/
theorem monomialChartPolynomialContainment_iff291
    (hk : B k = 0) (x : MonomialWholeIdealChart287 (A := A) B)
    (f : A →+* D) (p : MvPolynomial (Fin m) A) :
    cyclicPolynomialContainmentIdeal291 B k (monomialWholeIdealChartPoint287 B k hk x) p ≤
        RingHom.ker f ↔
      MvPolynomial.map f p ∈ x.val.map (MvPolynomial.map f) := by
  rw [cyclicPolynomialContainmentIdeal_le_ker_iff291,
    cyclicMatrixWholeIdealChart_map287 B k hk f,
    monomialWholeIdealChartPoint_chart287 B k hk]
  rfl

end PfaffianDescent
