import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace PfaffianDescent
open Polynomial

section
variable (K : Type*) [Field K] [NeZero (2 : K)]

/-- The quadratic coordinate algebra of the displayed good incidence fiber. -/
noncomputable def goodFiberPolynomial : K[X] := X ^ 2 + C 2
abbrev GoodFiberQuadratic := AdjoinRoot (goodFiberPolynomial K)

lemma goodFiberPolynomial_monic : (goodFiberPolynomial K).Monic :=
  Polynomial.monic_X_pow_add_C _ (by decide)

lemma goodFiberPolynomial_natDegree : (goodFiberPolynomial K).natDegree = 2 := by
  simp [goodFiberPolynomial]

instance : FiniteDimensional K (GoodFiberQuadratic K) :=
  (goodFiberPolynomial_monic K).finite_adjoinRoot

lemma goodFiberQuadratic_finrank : Module.finrank K (GoodFiberQuadratic K) = 2 := by
  change Module.finrank K (K[X] ⧸ Ideal.span {goodFiberPolynomial K}) = 2
  rw [finrank_quotient_span_eq_natDegree, goodFiberPolynomial_natDegree]

/-- A standard étale presentation: the derivative and the quadratic generate one. -/
noncomputable def goodFiberEtalePair : StandardEtalePair K where
  f := goodFiberPolynomial K
  monic_f := goodFiberPolynomial_monic K
  g := 1
  cond := by
    refine ⟨C (-(1 / 4 : K)) * X, C (1 / 2 : K), 0, ?_⟩
    simp only [goodFiberPolynomial, derivative_add, derivative_pow, derivative_X,
      derivative_C, pow_zero, add_zero, pow_one, mul_one]
    have h4 : (4 : K) ≠ 0 := by
      rw [show (4 : K) = 2 * 2 by norm_num]
      exact mul_ne_zero (NeZero.ne (2 : K)) (NeZero.ne (2 : K))
    have h2 : (2 : K) ≠ 0 := NeZero.ne (2 : K)
    have hcoeff : (2 : K) * (-(1 / 4 : K)) + 1 / 2 = 0 := by field_simp; ring
    have hconst : (2 : K) * (1 / 2 : K) = 1 := by field_simp
    calc
      _ = C ((2 : K) * (-(1 / 4 : K)) + 1 / 2) * X ^ 2 +
          C ((2 : K) * (1 / 2 : K)) := by
        simp only [map_add, map_mul]
        norm_num
        ring
      _ = 1 := by rw [hcoeff, hconst]; simp

/-- The standard étale ring is isomorphic to the quadratic algebra itself:
localizing at one makes no change. -/
noncomputable def goodFiberStandardEquiv : (goodFiberEtalePair K).Ring ≃ₐ[K] GoodFiberQuadratic K := by
  let e := (goodFiberEtalePair K).equivAwayAdjoinRoot
  have e' : (goodFiberEtalePair K).Ring ≃ₐ[K]
      Localization.Away (1 : GoodFiberQuadratic K) := by
    change (goodFiberEtalePair K).Ring ≃ₐ[K]
      Localization.Away (1 : AdjoinRoot (goodFiberPolynomial K))
    have he : AdjoinRoot.mk (goodFiberPolynomial K) (1 : K[X]) = 1 := map_one _
    rw [← he]
    exact e
  exact e'.trans ((IsLocalization.atOne (GoodFiberQuadratic K)
    (Localization.Away (1 : GoodFiberQuadratic K))).restrictScalars K).symm

instance : Algebra.Etale K (GoodFiberQuadratic K) :=
  Algebra.Etale.of_equiv (goodFiberStandardEquiv K)

lemma goodFiberQuadratic_root_relation :
    AdjoinRoot.root (goodFiberPolynomial K) ^ 2 + 2 = 0 := by
  have h := AdjoinRoot.eval₂_root (goodFiberPolynomial K)
  change (X ^ 2 + C (2 : K)).eval₂ (AdjoinRoot.of (goodFiberPolynomial K))
    (AdjoinRoot.root (goodFiberPolynomial K)) = 0 at h
  rw [eval₂_add, eval₂_pow, eval₂_X, eval₂_C] at h
  simpa only [map_ofNat] using h

end
end PfaffianDescent
