import PfaffianDescent.CorayHomogeneousComponentOriginalClosedPoint
import PfaffianDescent.CoraySelectedComponentHeightAndRelevance
import PfaffianDescent.CorayRelevantPrimeComponentHyperplaneDegree
import Mathlib.RingTheory.Ideal.Height

/-! A genuine lower-degree section through the original point supplies a
SAME component of a padded product q of ORIGINAL degree a+b, with strict
own coordinate degree. No whole-Proj integrality converse or auxiliary
regularity/Bertini is used. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- SAME minimal component of (p,s) remains minimal for the literal (p,s*t).
Both original regular-pair heights2 are derived before strict-height
containment is used. No minimality or height of the product is assumed. -/
theorem cubic_nonzeroProduct_same_lowerComponent_minimalTransfer001
    (p s t : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (a b : ℕ)
    (hs : s.IsHomogeneous a) (ht : t.IsHomogeneous b)
    (hsnot : s ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (htnot : t ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p s hp hs).toIdeal.minimalPrimes) :
    C.toIdeal ∈ (projectiveIntersectionIdeal p (s * t) hp (hs.mul ht)).toIdeal.minimalPrimes := by
  letI : C.toIdeal.IsPrime := hCmin.isPrime
  have hpPrime := PfaffianDescent.principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0
  have hProductNot : s * t ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) := by
    intro h
    rcases hpPrime.mem_or_mem h with h | h
    · exact hsnot h
    · exact htnot h
  have hLowerSpan : Ideal.span ({p, s} : Set (MvPolynomial (Fin 4) K)) ≤ C.toIdeal := by
    simpa only [projectiveIntersectionIdeal_toIdeal] using hCmin.le
  have hContain : (projectiveIntersectionIdeal p (s * t) hp (hs.mul ht)).toIdeal ≤ C.toIdeal := by
    rw [projectiveIntersectionIdeal_toIdeal]
    apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact hLowerSpan (Ideal.subset_span (by simp))
    · obtain rfl := Set.mem_singleton_iff.mp hx
      exact C.toIdeal.mul_mem_right t (hLowerSpan (Ideal.subset_span (by simp)))
  obtain ⟨J, hJmin, _hPJ, hJC, hJprime⟩ :=
    homogeneousMinimalPrime_exists_le_prime
      (projectiveIntersectionIdeal p (s * t) hp (hs.mul ht)) C.toIdeal hContain
  letI : J.toIdeal.IsPrime := hJprime
  have hCHeight := selectedProjectiveMinimalComponent_homogeneous_height_eq_two
    p s hp hp0 a hs hsnot C hCmin
  have hJHeight := selectedProjectiveMinimalComponent_homogeneous_height_eq_two
    p (s * t) hp hp0 (a + b) (hs.mul ht) hProductNot J hJmin
  letI : J.toIdeal.FiniteHeight := ⟨Or.inr (by rw [hJHeight]; simp)⟩
  have hSame : J.toIdeal = C.toIdeal :=
    Ideal.eq_of_le_of_height_le J.toIdeal hJC (by rw [hCHeight, hJHeight])
  have hHomogeneousSame : J = C := HomogeneousIdeal.toIdeal_injective hSame
  simpa only [hHomogeneousSame] using hJmin

/-- A SAME original closed point on a genuine lower-degree p/s curve
internally chooses its minimal C, a linear H outside C and the literal
padded q=s*H^b. C is minimal for BOTH curves, has degree<3(a+b), and retains
its own degree-preserving residue-field lift of SAME original P. -/
theorem lowerDegree_originalClosedPoint_exists_same_paddedProduct_component_strictDegree001
    [Infinite K]
    (p s : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (a b : ℕ) (hb : 0 < b)
    (hs : s.IsHomogeneous a)
    (hsnot : s ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (P : closedPoints (scheme (projectiveIntersectionIdeal p s hp hs))) :
    ∃ (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
      (hIC : (projectiveIntersectionIdeal p s hp hs).toIdeal ≤ C.toIdeal)
      (H : MvPolynomial (Fin 4) K) (hH : H.IsHomogeneous 1),
      H ∉ C.toIdeal ∧
      let ht : (H ^ b).IsHomogeneous b := by simpa only [Nat.one_mul] using hH.pow b
      C.toIdeal ∈ (projectiveIntersectionIdeal p s hp hs).toIdeal.minimalPrimes ∧
      C.toIdeal ∈ (projectiveIntersectionIdeal p (s * H ^ b) hp (hs.mul ht)).toIdeal.minimalPrimes ∧
      actualCurveCoordinateHilbertDegree C < 3 * (a + b) ∧
      ∃ Q : closedPoints (scheme C),
        schemeQuotientMap (projectiveIntersectionIdeal p s hp hs) C hIC Q.1 = P.1 ∧
        IsIso ((schemeQuotientMap (projectiveIntersectionIdeal p s hp hs) C hIC).residueFieldMap Q.1) ∧
        (toBase C).residueDegree Q.1 =
          (toBase (projectiveIntersectionIdeal p s hp hs)).residueDegree P.1 := by
  classical
  obtain ⟨C, hIC, hCmin, hCprime, Q, hQpoint, hQiso, hQdegree⟩ :=
    homogeneousProjective_originalClosedPoint_exists_minimalComponent
      (projectiveIntersectionIdeal p s hp hs) P
  letI : C.toIdeal.IsPrime := hCprime
  have hCrel := selectedProjectiveMinimalComponent_homogeneous_relevant
    p s hp hp0 a hs hsnot C hCmin
  obtain ⟨H, hH, hHnot, _hFinite, _hHyperplaneRank, hDegreeBound, _N, _hIncrement⟩ :=
    selectedProjectiveRelevantPrime_exists_hyperplane_degree_bound
      p s hp hp0 a hs hsnot C hCrel hIC
  have ht : (H ^ b).IsHomogeneous b := by simpa only [Nat.one_mul] using hH.pow b
  have hPowerNot : H ^ b ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) := by
    intro h
    have hpLow : Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) ≤
        (projectiveIntersectionIdeal p s hp hs).toIdeal := le_sup_left
    have hPowC : H ^ b ∈ C.toIdeal := hIC (hpLow h)
    exact hHnot (hCprime.mem_of_pow_mem b hPowC)
  have hProductMin := cubic_nonzeroProduct_same_lowerComponent_minimalTransfer001
    p s (H ^ b) hp hp0 a b hs ht hsnot hPowerNot C hCmin
  have hStrict : actualCurveCoordinateHilbertDegree C < 3 * (a + b) := by omega
  exact ⟨C, hIC, H, hH, hHnot, hCmin, hProductMin, hStrict,
    Q, hQpoint, hQiso, hQdegree⟩

end PfaffianDescent.Coray
