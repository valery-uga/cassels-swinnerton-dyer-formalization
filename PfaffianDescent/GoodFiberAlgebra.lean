import PfaffianDescent.GoodFiberQuadratic
import PfaffianDescent.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.LinearCombination

namespace PfaffianDescent
open scoped BigOperators

section
variable (K : Type*) [Field K]

/-- The three equations in the affine chart of the displayed incidence fiber. -/
noncomputable def goodFiberRelations : Fin 3 → MvPolynomial (Fin 3) K :=
  ![1 + MvPolynomial.X 0 * MvPolynomial.X 1,
    1 + MvPolynomial.X 0 * MvPolynomial.X 2,
    1 + 2 * MvPolynomial.X 1 * MvPolynomial.X 2]

noncomputable def goodFiberIdeal : Ideal (MvPolynomial (Fin 3) K) :=
  Ideal.span (Set.range (goodFiberRelations K))

abbrev GoodFiberAlgebra := MvPolynomial (Fin 3) K ⧸ goodFiberIdeal K

end

namespace GoodFiberAlgebra
section
variable {K : Type*} [Field K] [NeZero (2 : K)]

noncomputable def x (i : Fin 3) : GoodFiberAlgebra K :=
  Ideal.Quotient.mkₐ K (goodFiberIdeal K) (MvPolynomial.X i)

lemma relation (i : Fin 3) :
    Ideal.Quotient.mkₐ K (goodFiberIdeal K) (goodFiberRelations K i) = 0 := by
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)

lemma relations :
    1 + x (K := K) 0 * x 1 = 0 ∧
    1 + x (K := K) 0 * x 2 = 0 ∧
    1 + 2 * x (K := K) 1 * x 2 = 0 := by
  have h0 := relation (K := K) 0
  have h1 := relation (K := K) 1
  have h2 := relation (K := K) 2
  change Ideal.Quotient.mkₐ K (goodFiberIdeal K)
    (1 + MvPolynomial.X 0 * MvPolynomial.X 1) = 0 at h0
  change Ideal.Quotient.mkₐ K (goodFiberIdeal K)
    (1 + MvPolynomial.X 0 * MvPolynomial.X 2) = 0 at h1
  change Ideal.Quotient.mkₐ K (goodFiberIdeal K)
    (1 + 2 * MvPolynomial.X 1 * MvPolynomial.X 2) = 0 at h2
  simpa only [map_add, map_one, map_mul, map_ofNat, x] using And.intro h0 (And.intro h1 h2)

lemma first_eq_twice_second : x (K := K) 0 = 2 * x 1 := by
  obtain ⟨h0, h1, h2⟩ := relations (K := K)
  linear_combination x (K := K) 0 * h2 - 2 * x (K := K) 1 * h1

lemma first_eq_twice_third : x (K := K) 0 = 2 * x 2 := by
  obtain ⟨h0, h1, h2⟩ := relations (K := K)
  linear_combination x (K := K) 0 * h2 - 2 * x (K := K) 2 * h0

lemma quadratic_relation : x (K := K) 0 ^ 2 + 2 = 0 := by
  have h := first_eq_twice_second (K := K)
  have h0 := (relations (K := K)).1
  linear_combination 2 * h0 + x (K := K) 0 * h

noncomputable def fromQuadratic : GoodFiberQuadratic K →ₐ[K] GoodFiberAlgebra K :=
  AdjoinRoot.liftAlgHom (goodFiberPolynomial K) (Algebra.ofId K _) (x 0) (by
    change (Polynomial.X ^ 2 + Polynomial.C (2 : K)).eval₂
      (Algebra.ofId K (GoodFiberAlgebra K)).toRingHom (x 0) = 0
    rw [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
    simpa only [map_ofNat] using quadratic_relation (K := K))

lemma fromQuadratic_root : fromQuadratic (AdjoinRoot.root (goodFiberPolynomial K)) = x (K := K) 0 :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

noncomputable def half : GoodFiberQuadratic K := algebraMap K _ (1 / 2 : K)

lemma twice_half : 2 * half (K := K) = 1 := by
  have h : (2 : K) * (1 / 2 : K) = 1 := by
    simpa only [div_eq_mul_inv, one_mul] using mul_inv_cancel₀ (NeZero.ne (2 : K))
  simpa only [map_mul, map_ofNat, map_one, half] using congrArg (algebraMap K (GoodFiberQuadratic K)) h

noncomputable def quadraticVariables : Fin 3 → GoodFiberQuadratic K :=
  let a := AdjoinRoot.root (goodFiberPolynomial K)
  ![a, half * a, half * a]

lemma quadraticVariables_relations (i : Fin 3) :
    MvPolynomial.aeval (quadraticVariables (K := K)) (goodFiberRelations K i) = 0 := by
  let a := AdjoinRoot.root (goodFiberPolynomial K)
  have ha : a ^ 2 + 2 = 0 := goodFiberQuadratic_root_relation K
  have hh := twice_half (K := K)
  have hunit : IsUnit (2 : GoodFiberQuadratic K) := by
    exact ⟨⟨2, half, hh, by simpa only [mul_comm] using hh⟩, rfl⟩
  have hleft : 1 + a * (half * a) = 0 := by
    apply hunit.mul_left_cancel
    linear_combination 2 * half (K := K) * ha - 2 * hh
  have hright : 1 + 2 * (half * a) * (half * a) = 0 := by
    linear_combination hleft + half (K := K) * a ^ 2 * hh
  fin_cases i
  · change MvPolynomial.aeval (quadraticVariables (K := K))
      (1 + MvPolynomial.X 0 * MvPolynomial.X 1) = 0
    simp only [map_add, map_one, map_mul, MvPolynomial.aeval_X]
    exact hleft
  · change MvPolynomial.aeval (quadraticVariables (K := K))
      (1 + MvPolynomial.X 0 * MvPolynomial.X 2) = 0
    simp only [map_add, map_one, map_mul, MvPolynomial.aeval_X]
    exact hleft
  · change MvPolynomial.aeval (quadraticVariables (K := K))
      (1 + 2 * MvPolynomial.X 1 * MvPolynomial.X 2) = 0
    simp only [map_add, map_one, map_mul, map_ofNat, MvPolynomial.aeval_X]
    exact hright

noncomputable def toQuadratic : GoodFiberAlgebra K →ₐ[K] GoodFiberQuadratic K :=
  Ideal.Quotient.liftₐ (goodFiberIdeal K) (MvPolynomial.aeval quadraticVariables) (by
    have hle : goodFiberIdeal K ≤
        RingHom.ker (MvPolynomial.aeval (quadraticVariables (K := K))).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact quadraticVariables_relations i
    intro a ha
    exact hle ha)

lemma toQuadratic_x (i : Fin 3) : toQuadratic (x (K := K) i) = quadraticVariables i := by
  change MvPolynomial.aeval (quadraticVariables (K := K)) (MvPolynomial.X i) = _
  exact MvPolynomial.aeval_X _ _

end
end GoodFiberAlgebra
end PfaffianDescent
