import AllCharacteristics.CubicPolynomialCoordinates
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Separable

/-!
# The finite algebra of a cubic line intersection

Restricting a cubic to a line gives a univariate polynomial of degree three
when the leading endpoint is not on the cubic. Its root algebra has dimension
three and supplies a solution of the original cubic, with a chosen unit
coordinate. No separability or reducedness hypothesis is imposed.
-/

open PfaffianDescent Polynomial
namespace AllCharacteristics
universe u

/-- The restriction of a cubic to the affine line `t a + b`. -/
noncomputable def cubicLinePolynomial {R : Type*} [CommRing R] {n : ℕ}
    (c : Cubic R n) (a b : Vec R n) : R[X] :=
  C (c.eval a) * X ^ 3 + C (c.mixed a b) * X ^ 2 +
    C (c.mixed b a) * X + C (c.eval b)

/-- Evaluation of the line polynomial is the evaluation of the cubic at the
corresponding affine-line point, over any coefficient extension ring. -/
theorem cubicLinePolynomial_eval₂
    {R A : Type*} [CommRing R] [CommRing A] {n : ℕ}
    (f : R →+* A) (c : Cubic R n) (a b : Vec R n) (t : A) :
    (cubicLinePolynomial c a b).eval₂ f t =
      (c.map f).eval (t • (fun i ↦ f (a i)) + (fun i ↦ f (b i))) := by
  rw [show t • (fun i ↦ f (a i)) + (fun i ↦ f (b i)) =
      t • (fun i ↦ f (a i)) + (1 : A) • (fun i ↦ f (b i)) by rw [one_smul],
    Cubic.eval_line, Cubic.eval_map, Cubic.eval_map, Cubic.mixed_map, Cubic.mixed_map]
  simp only [cubicLinePolynomial, eval₂_add, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X,
    one_pow, mul_one, one_mul]
  ring

/-- The line restriction has full degree three when its leading endpoint is
not a zero of the cubic. -/
theorem cubicLinePolynomial_natDegree
    {R : Type*} [CommRing R] {n : ℕ} (c : Cubic R n) (a b : Vec R n)
    (ha : c.eval a ≠ 0) : (cubicLinePolynomial c a b).natDegree = 3 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro m hm
    have hm0 : m ≠ 0 := by omega
    have hm1 : 1 ≠ m := by omega
    have hm2 : m ≠ 2 := by omega
    have hm3 : m ≠ 3 := by omega
    simp [cubicLinePolynomial, coeff_C_mul, coeff_X, coeff_C, hm0, hm1, hm2, hm3]
  · simpa [cubicLinePolynomial, coeff_C_mul] using ha

/-- If a cubic has no zero at the first coordinate point, its intersection
with the line through the first two coordinate points gives a nonzero solution
over a finite algebra of dimension three. The second coordinate is one. -/
theorem cubic_rank_three_algebra_solution
    {k : Type u} [Field k] {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (c : Cubic k n) (hi : c.eval (Pi.single i 1) ≠ 0) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra k A) (_ : Module.Finite k A),
      Module.finrank k A = 3 ∧ ∃ x : Fin n → A,
        x j = 1 ∧ (c.map (algebraMap k A)).eval x = 0 := by
  let a : Vec k n := Pi.single i 1
  let b : Vec k n := Pi.single j 1
  let F := cubicLinePolynomial c a b
  have hd : F.natDegree = 3 := cubicLinePolynomial_natDegree c a b hi
  have hF : F ≠ 0 := by
    intro h
    simp [h] at hd
  let A := AdjoinRoot F
  let pb := AdjoinRoot.powerBasis hF
  let : Module.Finite k A := Module.Finite.of_basis pb.basis
  have hdim : Module.finrank k A = 3 := pb.finrank.trans hd
  let x : Fin n → A :=
    AdjoinRoot.root F • (fun l ↦ algebraMap k A (a l)) + (fun l ↦ algebraMap k A (b l))
  refine ⟨A, inferInstance, inferInstance, inferInstance, hdim, x, ?_, ?_⟩
  · simp [x, a, b, Pi.single_eq_of_ne hij.symm]
  · rw [← cubicLinePolynomial_eval₂ (algebraMap k A) c a b (AdjoinRoot.root F)]
    exact AdjoinRoot.eval₂_root F

/-- A transverse affine line section of a cubic over an algebraically closed
field consists of three distinct points.  The separability premise records
transversality of the restricted cubic polynomial; the leading coefficient
condition rules out an intersection at the point at infinity of this affine
chart. -/
theorem exists_three_distinct_cubic_line_points_of_separable
    {K : Type u} [Field K] [IsAlgClosed K]
    (c : Cubic K 4) (a b : Vec K 4)
    (ha : c.eval a ≠ 0) (ha0 : a ≠ 0)
    (hsep : (cubicLinePolynomial c a b).Separable) :
    ∃ x : Fin 3 → Vec K 4,
      (∀ i, c.eval (x i) = 0) ∧ Function.Injective x := by
  classical
  let f := cubicLinePolynomial c a b
  have hdeg : f.natDegree = 3 := cubicLinePolynomial_natDegree c a b ha
  have hf0 : f ≠ 0 := by
    intro hf
    simp [hf] at hdeg
  have hcard : f.roots.toFinset.card = 3 := by
    rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep),
      IsAlgClosed.card_roots_eq_natDegree]
    exact hdeg
  have hcard' : Fintype.card {x : K // x ∈ f.roots.toFinset} = 3 := by
    simpa using hcard
  let e : Fin 3 ≃ {x : K // x ∈ f.roots.toFinset} :=
    (Fintype.equivFinOfCardEq hcard').symm
  refine ⟨fun i => (e i).val • a + b, ?_, ?_⟩
  · intro i
    have hi : (e i).val ∈ f.roots := by
      exact Multiset.mem_toFinset.mp (e i).property
    have hroot : f.eval (e i).val = 0 := (Polynomial.mem_roots hf0).mp hi
    have hroot' : f.eval₂ (RingHom.id K) (e i).val = 0 := by simpa using hroot
    rw [cubicLinePolynomial_eval₂ (RingHom.id K) c a b] at hroot'
    change c.eval ((e i).val • a + b) = 0 at hroot'
    exact hroot'
  · intro i j hij
    have hv : (e i).val • a = (e j).val • a := by
      apply add_right_cancel
      exact hij
    have hscalar : (e i : K) = e j := by
      obtain ⟨k, hk⟩ : ∃ k, a k ≠ 0 := by
        by_contra h
        push Not at h
        exact ha0 (funext h)
      have hk' := congrFun hv k
      simp only [Pi.smul_apply] at hk'
      exact mul_right_cancel₀ hk hk'
    apply e.injective
    apply Subtype.ext
    exact hscalar

/-- A separable cubic restriction has exactly three projective zeros on the
line spanned by `a,b`, including the point-at-infinity check supplied by
`c.eval a ≠ 0`. Every vector zero on that line is zero or a scalar multiple
of one of the three displayed roots. -/
theorem exists_three_cubic_line_points_cover_of_separable
    {K : Type u} [Field K] [IsAlgClosed K]
    (c : Cubic K 4) (a b : Vec K 4)
    (ha : c.eval a ≠ 0)
    (hsep : (cubicLinePolynomial c a b).Separable) :
    ∃ x : Fin 3 → Vec K 4,
      (∀ i, c.eval (x i) = 0) ∧
      Function.Injective x ∧
      (∀ i, ∃ t : K, x i = t • a + b) ∧
      ∀ s t : K, c.eval (s • a + t • b) = 0 →
        s • a + t • b = 0 ∨
          ∃ (i : Fin 3) (u : K), s • a + t • b = u • x i := by
  classical
  let f := cubicLinePolynomial c a b
  have hdeg : f.natDegree = 3 := cubicLinePolynomial_natDegree c a b ha
  have hf0 : f ≠ 0 := by
    intro hf
    simp [hf] at hdeg
  have hcard : f.roots.toFinset.card = 3 := by
    rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep),
      IsAlgClosed.card_roots_eq_natDegree]
    exact hdeg
  have hcard' : Fintype.card {z : K // z ∈ f.roots.toFinset} = 3 := by
    simpa using hcard
  let e : Fin 3 ≃ {z : K // z ∈ f.roots.toFinset} :=
    (Fintype.equivFinOfCardEq hcard').symm
  let x : Fin 3 → Vec K 4 := fun i => (e i).val • a + b
  refine ⟨x, ?_, ?_, ?_, ?_⟩
  · intro i
    have hi : (e i).val ∈ f.roots :=
      Multiset.mem_toFinset.mp (e i).property
    have hroot : f.eval (e i).val = 0 := (Polynomial.mem_roots hf0).mp hi
    have hroot' : f.eval₂ (RingHom.id K) (e i).val = 0 := by simpa using hroot
    rw [cubicLinePolynomial_eval₂ (RingHom.id K) c a b] at hroot'
    exact hroot'
  · intro i j hij
    have hv : (e i).val • a = (e j).val • a := by
      apply add_right_cancel
      exact hij
    have ha0 : a ≠ 0 := by
      intro hazero
      subst a
      exact ha (by simp)
    have hscalar : (e i : K) = e j := by
      obtain ⟨k, hk⟩ : ∃ k, a k ≠ 0 := by
        by_contra h
        push Not at h
        exact ha0 (funext h)
      have hk' := congrFun hv k
      simp only [Pi.smul_apply] at hk'
      exact mul_right_cancel₀ hk hk'
    apply e.injective
    apply Subtype.ext
    exact hscalar
  · intro i
    exact ⟨(e i).val, rfl⟩
  intro s t hzero
  by_cases ht : t = 0
  · subst t
    have hs : s = 0 := by
      have h := hzero
      simpa [Cubic.eval_smul, ha] using h
    subst s
    left
    simp
  · let z : K := s / t
    have hy : s • a + t • b = t • (z • a + b) := by
      ext j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      dsimp [z]
      field_simp [ht]
    have hz0 : c.eval (z • a + b) = 0 := by
      rw [hy, Cubic.eval_smul] at hzero
      exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero 3 ht)
    have hfz : f.eval z = 0 := by
      have h := cubicLinePolynomial_eval₂ (RingHom.id K) c a b z
      simpa using h.trans hz0
    have hzroots : z ∈ f.roots.toFinset := by
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hf0).mpr hfz)
    obtain ⟨i, hi⟩ := e.surjective (⟨z, hzroots⟩ : {z : K // z ∈ f.roots.toFinset})
    right
    refine ⟨i, t, ?_⟩
    rw [hy]
    have hzi : (e i).val = z := congrArg Subtype.val hi
    simp [x, hzi]

/-- Without separability, the distinct roots of a nonzero cubic line
restriction still form a finite set covering all projective zeros on the
line. Multiplicities play no role in this support statement. -/
theorem finite_cubic_line_points_cover
    {K : Type u} [Field K] [IsAlgClosed K] [DecidableEq K]
    (c : Cubic K 4) (a b : Vec K 4)
    (ha : c.eval a ≠ 0) :
    let f := cubicLinePolynomial c a b
    let T := {z : K // z ∈ f.roots.toFinset}
    (∀ z : T, c.eval (z.1 • a + b) = 0) ∧
    ∀ s t : K, c.eval (s • a + t • b) = 0 →
      s • a + t • b = 0 ∨
        ∃ (z : T) (u : K), s • a + t • b = u • (z.1 • a + b) := by
  classical
  let f := cubicLinePolynomial c a b
  have hdeg : f.natDegree = 3 := cubicLinePolynomial_natDegree c a b ha
  have hf0 : f ≠ 0 := by
    intro hf
    simp [hf] at hdeg
  constructor
  · intro z
    have hz : f.eval z.1 = 0 :=
      (Polynomial.mem_roots hf0).mp (Multiset.mem_toFinset.mp z.2)
    have hroot' : f.eval₂ (RingHom.id K) z.1 = 0 := by simpa using hz
    rw [cubicLinePolynomial_eval₂ (RingHom.id K) c a b] at hroot'
    exact hroot'
  · intro s t hzero
    by_cases ht : t = 0
    · subst t
      have hs : s = 0 := by
        have h := hzero
        simpa [Cubic.eval_smul, ha] using h
      subst s
      left
      simp
    · let z : K := s / t
      have hy : s • a + t • b = t • (z • a + b) := by
        ext j
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        dsimp [z]
        field_simp [ht]
      have hz0 : c.eval (z • a + b) = 0 := by
        rw [hy, Cubic.eval_smul] at hzero
        exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero 3 ht)
      have hfz : f.eval z = 0 := by
        have h := cubicLinePolynomial_eval₂ (RingHom.id K) c a b z
        simpa using h.trans hz0
      have hzroots : z ∈ f.roots.toFinset :=
        Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hf0).mpr hfz)
      exact Or.inr ⟨⟨z, hzroots⟩, t, hy⟩

/-- A cubic line restriction with nonzero leading endpoint has at least one
affine root over an algebraically closed field, even with multiplicity. -/
theorem cubicLinePolynomial_exists_root
    {K : Type u} [Field K] [IsAlgClosed K]
    (c : Cubic K 4) (a b : Vec K 4)
    (ha : c.eval a ≠ 0) :
    ∃ t : K, (cubicLinePolynomial c a b).eval t = 0 := by
  let f := cubicLinePolynomial c a b
  have hdeg : f.natDegree = 3 := cubicLinePolynomial_natDegree c a b ha
  have hf0 : f ≠ 0 := by
    intro hf
    simp [hf] at hdeg
  have hcard : f.roots.card = 3 := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hdeg]
  have hroots : f.roots ≠ 0 := by
    intro h
    simp [h] at hcard
  obtain ⟨t, ht⟩ := Multiset.exists_mem_of_ne_zero hroots
  exact ⟨t, (Polynomial.mem_roots hf0).mp ht⟩

end AllCharacteristics
