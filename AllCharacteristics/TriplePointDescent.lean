import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Descent from a triple point

The non-characteristic-three part of the triple-point argument only needs
faithful descent of a finite linear relation.  The proof below is elementary:
apply a ground-field linear functional which is nonzero on one chosen
coordinate of the relation.  This avoids any separability assumption on the
finite extension.
-/

open scoped BigOperators
namespace AllCharacteristics

universe u v

/-- A nonzero relation among vectors with ground-field coordinates, found
after extending the field, already gives a nonzero relation over the ground
field.  No finiteness or separability hypothesis on the extension is needed. -/
theorem exists_ground_relation_of_extension_relation
    {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]
    {ι : Type*} [Fintype ι] {κ : Type*}
    (A : κ → ι → k) (x : ι → L) (hx : x ≠ 0)
    (hrel : ∀ j, ∑ i, algebraMap k L (A j i) * x i = 0) :
    ∃ y : ι → k, y ≠ 0 ∧ ∀ j, ∑ i, A j i * y i = 0 := by
  classical
  have hex : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hex
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k hi
  let y : ι → k := fun j => φ (x j)
  refine ⟨y, ?_, ?_⟩
  · intro hy
    have := congrFun hy i
    simp [y, hφ] at this
  · intro j
    have h := congrArg φ (hrel j)
    simpa [y, ← Algebra.smul_def] using h

/-- The directional derivative of a multivariate polynomial in a constant
vector direction. -/
noncomputable def directionalDerivative {K : Type*} [CommRing K] {n : ℕ}
    (p : MvPolynomial (Fin n) K) (x : Fin n → K) : MvPolynomial (Fin n) K :=
  ∑ i, MvPolynomial.C (x i) * MvPolynomial.pderiv i p

/-- A nonzero direction annihilating all first derivatives after field
extension descends to such a direction over the ground field. -/
theorem exists_ground_directionalDerivative_zero
    {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L] {n : ℕ}
    (p : MvPolynomial (Fin n) k) (x : Fin n → L) (hx : x ≠ 0)
    (hdir : ∑ i, MvPolynomial.C (x i) *
        (MvPolynomial.pderiv i p).map (algebraMap k L) = 0) :
    ∃ y : Fin n → k, y ≠ 0 ∧ directionalDerivative p y = 0 := by
  classical
  obtain ⟨y, hy, hrel⟩ := exists_ground_relation_of_extension_relation
    (fun d i => MvPolynomial.coeff d (MvPolynomial.pderiv i p)) x hx (fun d => by
      have h := congrArg (MvPolynomial.coeff d) hdir
      simpa only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
        MvPolynomial.coeff_map, MvPolynomial.coeff_zero, mul_comm] using h)
  refine ⟨y, hy, ?_⟩
  ext d
  simpa only [directionalDerivative, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_C_mul, MvPolynomial.coeff_zero, mul_comm] using hrel d

/-- Euler's identity turns a nonzero ground-field translation direction of a
homogeneous cubic into a rational point when the characteristic is not three. -/
theorem cubic_eval_eq_zero_of_directionalDerivative_zero
    {k : Type u} [Field k] {n : ℕ}
    (p : MvPolynomial (Fin n) k) (hp : p.IsHomogeneous 3)
    (y : Fin n → k) (hdir : directionalDerivative p y = 0)
    (hthree : (3 : k) ≠ 0) : p.eval y = 0 := by
  have hzero : 3 • p.eval y = 0 := by
    calc
      3 • p.eval y = MvPolynomial.eval y (3 • p) := by simp
      _ = MvPolynomial.eval y
          (∑ i, MvPolynomial.X i * MvPolynomial.pderiv i p) := by
            rw [hp.sum_X_mul_pderiv]
      _ = MvPolynomial.eval y (directionalDerivative p y) := by
            simp [directionalDerivative]
      _ = 0 := by rw [hdir]; simp
  have hmul : (3 : k) * p.eval y = 0 := by
    simpa [nsmul_eq_mul] using hzero
  exact (mul_eq_zero.mp hmul).resolve_left hthree

/-- The characteristic-not-three conclusion of the paper's triple-point
argument, stated at the exact directional-derivative boundary supplied by the
multiplicity calculation. -/
theorem exists_ground_cubic_point_of_extension_direction
    {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L] {n : ℕ}
    (p : MvPolynomial (Fin n) k) (hp : p.IsHomogeneous 3)
    (hthree : (3 : k) ≠ 0)
    (x : Fin n → L) (hx : x ≠ 0)
    (hdir : ∑ i, MvPolynomial.C (x i) *
        (MvPolynomial.pderiv i p).map (algebraMap k L) = 0) :
    ∃ y : Fin n → k, y ≠ 0 ∧ p.eval y = 0 := by
  obtain ⟨y, hy, hdy⟩ := exists_ground_directionalDerivative_zero p x hx hdir
  exact ⟨y, hy, cubic_eval_eq_zero_of_directionalDerivative_zero p hp y hdy hthree⟩

/-- In characteristic three, a finite extension whose degree is prime to
three is separable.  This isolates the field-theoretic input needed for the
trace branch of the paper's triple-point argument. -/
theorem isSeparable_of_finrank_coprime_three
    {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [CharP k 3]
    (hdegree : Nat.Coprime (Module.finrank k L) 3) :
    Algebra.IsSeparable k L := by
  rw [isSeparable_iff_finInsepDegree_eq_one]
  obtain ⟨m, hm⟩ := finInsepDegree_eq_pow k L 3
  cases m with
  | zero => simpa using hm
  | succ m =>
      exfalso
      have hthree_insep : 3 ∣ Field.finInsepDegree k L := by
        rw [hm, pow_succ]
        simp
      have hinsep_degree : Field.finInsepDegree k L ∣ Module.finrank k L := by
        use Field.finSepDegree k L
        rw [← Field.finSepDegree_mul_finInsepDegree]
        exact Nat.mul_comm _ _
      have hthree_degree : 3 ∣ Module.finrank k L :=
        dvd_trans hthree_insep hinsep_degree
      have hbad : Nat.Coprime 3 3 := hdegree.of_dvd_left hthree_degree
      simp at hbad

/-- Coordinatewise field trace. -/
noncomputable def traceVector
    {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] {n : ℕ} (x : Fin n → L) : Fin n → k :=
  fun i => Algebra.trace k L (x i)

/-- A coordinate normalized to one makes the trace vector nonzero whenever
the extension degree is prime to three in characteristic three. -/
theorem traceVector_ne_zero_of_coordinate_eq_one
    {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [CharP k 3] {n : ℕ}
    (hdegree : Nat.Coprime (Module.finrank k L) 3)
    (x : Fin n → L) (i : Fin n) (hi : x i = 1) :
    traceVector (k := k) x ≠ 0 := by
  have hcast : (Module.finrank k L : k) ≠ 0 := by
    intro hzero
    have hdiv : 3 ∣ Module.finrank k L :=
      (CharP.cast_eq_zero_iff k 3 _).mp hzero
    have hbad : Nat.Coprime 3 3 := hdegree.of_dvd_left hdiv
    simp at hbad
  intro hx
  have hxi := congrFun hx i
  simp [traceVector, hi] at hxi
  have htrace : Algebra.trace k L (1 : L) = (Module.finrank k L : k) := by
    rw [show (1 : L) = algebraMap k L (1 : k) by simp, Algebra.trace_algebraMap]
    simp
  rw [htrace] at hxi
  exact hcast hxi

/-- Over an algebraically closed overfield, the image of the trace vector is
the sum of the conjugate vectors. -/
theorem algebraMap_traceVector_eq_sum_embeddings
    {k : Type u} {L : Type v} {E : Type*}
    [Field k] [Field L] [Field E] [Algebra k L] [Algebra k E]
    [FiniteDimensional k L] [Algebra.IsSeparable k L] [IsAlgClosed E]
    {n : ℕ} (x : Fin n → L) :
    (fun i => algebraMap k E (traceVector (k := k) x i)) =
      ∑ σ : L →ₐ[k] E, fun i => σ (x i) := by
  funext i
  simpa [traceVector] using trace_eq_sum_embeddings E (x := x i)

/-- Any additive family of directions which contains every conjugate of a
vector also contains the embedded coordinatewise trace.  This is the exact
additivity step used for translation directions in characteristic three. -/
theorem traceVector_mem_of_embeddings_mem
    {k : Type u} {L : Type v} {E : Type*}
    [Field k] [Field L] [Field E] [Algebra k L] [Algebra k E]
    [FiniteDimensional k L] [Algebra.IsSeparable k L] [IsAlgClosed E]
    {n : ℕ} (W : AddSubgroup (Fin n → E)) (x : Fin n → L)
    (hconj : ∀ σ : L →ₐ[k] E, (fun i => σ (x i)) ∈ W) :
    (fun i => algebraMap k E (traceVector (k := k) x i)) ∈ W := by
  rw [algebraMap_traceVector_eq_sum_embeddings]
  exact W.sum_mem fun σ _ => hconj σ

end AllCharacteristics
