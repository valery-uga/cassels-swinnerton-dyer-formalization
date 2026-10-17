import PfaffianDescent.CyclicPolynomialActionFreeQuotient281

/- Finite border generators for the entire cyclic polynomial action kernel.
No radical, flatness, or ideal-equality premise occurs. -/
noncomputable section
namespace PfaffianDescent
open MvPolynomial
open scoped BigOperators
universe u
variable {R : Type u} [CommRing R] {m n : ℕ}

def cyclicMonomialLift285 (B : Fin n → (Fin m →₀ ℕ)) :
    (Fin n → R) →ₗ[R] MvPolynomial (Fin m) R where
  toFun x := ∑ j : Fin n, x j • monomial (B j) 1
  map_add' x y := by simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [Pi.smul_apply, smul_smul, Finset.smul_sum]

lemma cyclicMonomialLift_single285 (B : Fin n → (Fin m →₀ ℕ)) (j : Fin n) :
    cyclicMonomialLift285 (R := R) B (Pi.single j 1) = monomial (B j) 1 := by
  classical
  simp [cyclicMonomialLift285, Pi.single_apply]

def cyclicActionBorderRelation285
    (rho : MvPolynomial (Fin m) R →ₐ[R] Module.End R (Fin n → R))
    (B : Fin n → (Fin m →₀ ℕ)) (q : Fin m × Fin n) : MvPolynomial (Fin m) R :=
  X q.1 * monomial (B q.2) 1 -
    cyclicMonomialLift285 B (rho (X q.1) (Pi.single q.2 1))

def cyclicActionUnitRelation285 (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n) :
    MvPolynomial (Fin m) R := monomial (B k) 1 - 1

lemma cyclicActionUnitRelation_zero285 (B : Fin n → (Fin m →₀ ℕ))
    (k : Fin n) (hk : B k = 0) : cyclicActionUnitRelation285 (R := R) B k = 0 := by
  rw [cyclicActionUnitRelation285, hk, MvPolynomial.monomial_zero', map_one, sub_self]

def cyclicActionGeneratorIdeal285
    (rho : MvPolynomial (Fin m) R →ₐ[R] Module.End R (Fin n → R))
    (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n) : Ideal (MvPolynomial (Fin m) R) :=
  Ideal.span (insert (cyclicActionUnitRelation285 B k)
    (Set.range (cyclicActionBorderRelation285 rho B)))

lemma cyclicActionGeneratorIdeal_fg285
    (rho : MvPolynomial (Fin m) R →ₐ[R] Module.End R (Fin n → R))
    (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n) :
    (cyclicActionGeneratorIdeal285 rho B k).FG := by
  change (Submodule.span (MvPolynomial (Fin m) R)
    (insert (cyclicActionUnitRelation285 B k)
      (Set.range (cyclicActionBorderRelation285 rho B)))).FG
  exact Submodule.fg_span ((Set.finite_range _).insert _)

lemma polynomialCyclicEvaluation_mul285
    (rho : MvPolynomial (Fin m) R →ₐ[R] Module.End R (Fin n → R))
    (v : Fin n → R) (p q : MvPolynomial (Fin m) R) :
    polynomialCyclicEvaluation281 rho v (p * q) =
      rho p (polynomialCyclicEvaluation281 rho v q) := by
  change rho (p * q) v = rho p (rho q v)
  rw [map_mul]
  rfl

lemma polynomialCyclicEvaluation_lift285
    (rho : MvPolynomial (Fin m) R →ₐ[R] Module.End R (Fin n → R))
    (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n)
    (hB : ∀ j, rho (monomial (B j) 1) (Pi.single k 1) = Pi.single j 1)
    (x : Fin n → R) :
    polynomialCyclicEvaluation281 rho (Pi.single k 1) (cyclicMonomialLift285 B x) = x := by
  classical
  change polynomialCyclicEvaluation281 rho (Pi.single k 1)
    (∑ j : Fin n, x j • monomial (B j) 1) = x
  simp only [map_sum, map_smul, polynomialCyclicEvaluation_apply281, hB]
  funext j
  simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]

lemma cyclicActionGeneratorIdeal_le_kernel285
    (rho : MvPolynomial (Fin m) R →ₐ[R] Module.End R (Fin n → R))
    (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n)
    (hB : ∀ j, rho (monomial (B j) 1) (Pi.single k 1) = Pi.single j 1) :
    cyclicActionGeneratorIdeal285 rho B k ≤ RingHom.ker rho.toRingHom := by
  apply Ideal.span_le.mpr
  intro p hp
  apply RingHom.mem_ker.mpr
  apply (polynomialCyclicEvaluation_zero_iff281 rho (Pi.single k 1) B hB p).mp
  rcases hp with rfl | ⟨⟨i, j⟩, rfl⟩
  · change rho (monomial (B k) 1 - 1) (Pi.single k 1) = 0
    rw [map_sub, LinearMap.sub_apply, hB, map_one, Module.End.one_apply, sub_self]
  · rw [cyclicActionBorderRelation285, map_sub, polynomialCyclicEvaluation_mul285,
      polynomialCyclicEvaluation_apply281, hB, polynomialCyclicEvaluation_lift285 rho B k hB,
      sub_self]


/-- Polynomial induction performed before specializing the quotient ring. -/
lemma polynomialCyclicNormalForm285
    {A : Type*} [CommRing A] [Algebra R A]
    (rho : MvPolynomial (Fin m) R →ₐ[R] Module.End R (Fin n → R))
    (v : Fin n → R) (q : MvPolynomial (Fin m) R →ₐ[R] A)
    (N : (Fin n → R) →ₗ[R] A) (hunit : N v = 1)
    (hX : ∀ i x, q (X i) * N x = N (rho (X i) x))
    (p : MvPolynomial (Fin m) R) :
    q p = N (polynomialCyclicEvaluation281 rho v p) := by
  induction p using MvPolynomial.induction_on with
  | C r =>
      rw [MvPolynomial.C_eq_smul_one, map_smul, map_one, map_smul,
        polynomialCyclicEvaluation_apply281, map_one, Module.End.one_apply,
        map_smul, hunit]
  | add p q hp hq =>
      rw [map_add, map_add, map_add, hp, hq]
  | mul_X p i hp =>
      rw [mul_comm p (X i), map_mul, polynomialCyclicEvaluation_mul285, ← hX, hp]

/-- Normal forms in the quotient by the primitive border and unit relations. -/
lemma cyclicActionGeneratorQuotient_normal285
    (rho : MvPolynomial (Fin m) R →ₐ[R] Module.End R (Fin n → R))
    (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n)
    (p : MvPolynomial (Fin m) R) :
    Ideal.Quotient.mk (cyclicActionGeneratorIdeal285 rho B k) p =
      Ideal.Quotient.mk (cyclicActionGeneratorIdeal285 rho B k)
        (cyclicMonomialLift285 B (polynomialCyclicEvaluation281 rho (Pi.single k 1) p)) := by
  classical
  let G := cyclicActionGeneratorIdeal285 rho B k
  let q : MvPolynomial (Fin m) R →ₐ[R] (MvPolynomial (Fin m) R ⧸ G) :=
    Ideal.Quotient.mkₐ R G
  let N : (Fin n → R) →ₗ[R] (MvPolynomial (Fin m) R ⧸ G) :=
    q.toLinearMap.comp (cyclicMonomialLift285 B)
  have hunit : N (Pi.single k 1) = 1 := by
    change q (cyclicMonomialLift285 B (Pi.single k 1)) = 1
    rw [cyclicMonomialLift_single285]
    have hz : q (cyclicActionUnitRelation285 B k) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert _ _))
    change q (monomial (B k) 1 - 1) = 0 at hz
    rw [map_sub] at hz
    have hqone : q (1 : MvPolynomial (Fin m) R) = 1 := map_one q
    rw [hqone] at hz
    exact sub_eq_zero.mp hz
  have hX : ∀ i x, q (X i) * N x = N (rho (X i) x) := by
    intro i
    have hlin : (LinearMap.mulLeft R (q (X i))).comp N = N.comp (rho (X i)) := by
      apply (Pi.basisFun R (Fin n)).ext
      intro j
      simp only [Pi.basisFun_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply]
      change q (X i) * q (cyclicMonomialLift285 B (Pi.single j 1)) =
        q (cyclicMonomialLift285 B (rho (X i) (Pi.single j 1)))
      rw [cyclicMonomialLift_single285]
      have hz : q (cyclicActionBorderRelation285 rho B (i, j)) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_range_self (i, j))))
      change q (X i * monomial (B j) 1 -
        cyclicMonomialLift285 B (rho (X i) (Pi.single j 1))) = 0 at hz
      rw [map_sub, map_mul, sub_eq_zero] at hz
      exact hz
    intro x
    exact congrArg (fun L : (Fin n → R) →ₗ[R] (MvPolynomial (Fin m) R ⧸ G) => L x) hlin
  exact polynomialCyclicNormalForm285 rho (Pi.single k 1) q N hunit hX p

lemma cyclicActionKernel_le_generatorIdeal285
    (rho : MvPolynomial (Fin m) R →ₐ[R] Module.End R (Fin n → R))
    (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n) :
    RingHom.ker rho.toRingHom ≤ cyclicActionGeneratorIdeal285 rho B k := by
  intro p hp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [cyclicActionGeneratorQuotient_normal285]
  have he : polynomialCyclicEvaluation281 rho (Pi.single k 1) p = 0 := by
    have hr : rho p = 0 := RingHom.mem_ker.mp hp
    rw [polynomialCyclicEvaluation_apply281, hr]
    rfl
  rw [he, map_zero, map_zero]

/-- The whole ideal, including its nilpotent structure, has these finite generators. -/
lemma cyclicActionKernel_eq_generatorIdeal285
    (rho : MvPolynomial (Fin m) R →ₐ[R] Module.End R (Fin n → R))
    (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n)
    (hB : ∀ j, rho (monomial (B j) 1) (Pi.single k 1) = Pi.single j 1) :
    RingHom.ker rho.toRingHom = cyclicActionGeneratorIdeal285 rho B k :=
  le_antisymm (cyclicActionKernel_le_generatorIdeal285 rho B k)
    (cyclicActionGeneratorIdeal_le_kernel285 rho B k hB)

lemma cyclicActionKernel_fg285
    (rho : MvPolynomial (Fin m) R →ₐ[R] Module.End R (Fin n → R))
    (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n)
    (hB : ∀ j, rho (monomial (B j) 1) (Pi.single k 1) = Pi.single j 1) :
    (RingHom.ker rho.toRingHom).FG := by
  rw [cyclicActionKernel_eq_generatorIdeal285 rho B k hB]
  exact cyclicActionGeneratorIdeal_fg285 rho B k

end PfaffianDescent
