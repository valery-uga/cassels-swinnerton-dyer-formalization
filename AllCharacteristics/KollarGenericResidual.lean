import AllCharacteristics.KollarAffineLine
import AllCharacteristics.CubicLineAlgebra
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# The generic residual polynomial in Kollár's line construction

The coordinate change which makes the first homogeneous coordinate the
polynomial variable turns the cubic equation into the reverse of the residual
quadratic on the universal line through `[1 : 0 : 0 : 0]`.  This file records
the small algebraic pieces of that identification separately, so they can be
combined without unfolding the full multivariate expression.
-/

namespace AllCharacteristics

open PfaffianDescent MvPolynomial
open Polynomial
open AlgebraicGeometry HomogeneousProjective

universe u v

abbrev KollarProjectiveDirectionRing (K : Type u) [CommRing K] :=
  MvPolynomial (Fin 3) K

noncomputable def kollarProjectiveDirectionCubic
    {K : Type u} [Field K] (c : Cubic K 4) :
    Cubic (KollarProjectiveDirectionRing K) 4 :=
  c.map MvPolynomial.C

noncomputable def kollarProjectiveDirectionBase
    (K : Type u) [Field K] :
    Fin 4 → KollarProjectiveDirectionRing K :=
  fun i => MvPolynomial.C (kollarBasePoint K i)

noncomputable def kollarUniversalResidualPolynomial
    {K : Type u} [Field K] (c : Cubic K 4) :
    (KollarProjectiveDirectionRing K)[X] :=
  Cubic.lineResidualPolynomial (kollarProjectiveDirectionCubic c)
    (kollarProjectiveDirectionBase K)
    (kollarProjectiveLinePolynomialDirection K)

noncomputable def kollarDistinguishedCoordinatePolynomial
    {K : Type u} [Field K] (c : Cubic K 4) :
    (KollarProjectiveDirectionRing K)[X] :=
  MvPolynomial.finSuccEquiv K 3 c.toMvPolynomial

noncomputable def kollarUniversalLineEvaluationPolynomial
    {K : Type u} [Field K] (c : Cubic K 4) :
    (KollarProjectiveDirectionRing K)[X] :=
  ((kollarProjectiveDirectionCubic c).map
    (Polynomial.C : KollarProjectiveDirectionRing K →+*
      (KollarProjectiveDirectionRing K)[X])).eval
      ((Polynomial.X : (KollarProjectiveDirectionRing K)[X]) •
        (fun i => Polynomial.C (kollarProjectiveDirectionBase K i)) +
      1 • (fun i => Polynomial.C (kollarProjectiveLinePolynomialDirection K i)))

noncomputable def kollarExplicitLinePolynomial
    {K : Type u} [Field K] (c : Cubic K 4) :
    (KollarProjectiveDirectionRing K)[X] :=
  (Polynomial.X : (KollarProjectiveDirectionRing K)[X]) ^ 3 *
      Polynomial.C ((kollarProjectiveDirectionCubic c).eval
        (kollarProjectiveDirectionBase K)) +
    Polynomial.X ^ 2 *
      Polynomial.C ((kollarProjectiveDirectionCubic c).mixed
        (kollarProjectiveDirectionBase K)
        (kollarProjectiveLinePolynomialDirection K)) +
    Polynomial.X *
      Polynomial.C ((kollarProjectiveDirectionCubic c).mixed
        (kollarProjectiveLinePolynomialDirection K)
        (kollarProjectiveDirectionBase K)) +
    Polynomial.C ((kollarProjectiveDirectionCubic c).eval
      (kollarProjectiveLinePolynomialDirection K))

/-- Reversing a genuine residual quadratic interchanges its three line
coefficients. -/
theorem kollar_reverse_lineResidualPolynomial
    {K : Type u} [CommRing K] [NoZeroDivisors K]
    (c : Cubic K 4) (p d : Fin 4 → K)
    (hdir : c.eval d ≠ 0) :
    (Cubic.lineResidualPolynomial c p d).reverse =
      Polynomial.C (c.eval d) + Polynomial.C (c.mixed d p) * Polynomial.X +
        Polynomial.C (c.mixed p d) * Polynomial.X ^ 2 := by
  let q := Cubic.lineResidualPolynomial c p d
  have hdeg : q.natDegree = 2 := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
      intro m hm
      have hm0 : m ≠ 0 := by omega
      have hm1' : 1 ≠ m := by omega
      have hm2 : m ≠ 2 := by omega
      simp [q, Cubic.lineResidualPolynomial, Polynomial.coeff_C_mul,
        Polynomial.coeff_X, Polynomial.coeff_C, hm0, hm1', hm2]
    · simpa [q, Cubic.lineResidualPolynomial,
        Polynomial.coeff_C_mul] using hdir
  ext n
  rw [Polynomial.coeff_reverse, hdeg]
  by_cases hn : n ≤ 2
  · interval_cases n
    · rw [Polynomial.revAt_le (by omega)]
      norm_num [q, Cubic.lineResidualPolynomial]
    · rw [Polynomial.revAt_le (by omega)]
      norm_num [q, Cubic.lineResidualPolynomial]
    · rw [Polynomial.revAt_le (by omega)]
      norm_num [q, Cubic.lineResidualPolynomial]
  · have hn' : 2 < n := Nat.lt_of_not_ge hn
    rw [Polynomial.revAt_eq_self_of_lt hn']
    simp [Cubic.lineResidualPolynomial, show n ≠ 2 by omega]
    rw [Polynomial.coeff_C_of_ne_zero (by omega),
      Polynomial.coeff_C_of_ne_zero (by omega)]

/-- `finSuccEquiv` evaluates the cubic tensor in the universal coordinates
`(T,u₀,u₁,u₂)`. -/
theorem kollar_finSucc_cubic_eq_universal_eval
    {K : Type u} [Field K] (c : Cubic K 4) :
    MvPolynomial.finSuccEquiv K 3 c.toMvPolynomial =
      (c.map ((Polynomial.C : MvPolynomial (Fin 3) K →+*
        (MvPolynomial (Fin 3) K)[X]).comp MvPolynomial.C)).eval
        (fun i => Fin.cases Polynomial.X
          (fun j => Polynomial.C (MvPolynomial.X j)) i) := by
  rw [MvPolynomial.finSuccEquiv_apply]
  change MvPolynomial.eval₂ ((Polynomial.C : MvPolynomial (Fin 3) K →+*
    (MvPolynomial (Fin 3) K)[X]).comp MvPolynomial.C)
    (fun i => Fin.cases Polynomial.X (fun j => Polynomial.C (MvPolynomial.X j)) i)
    c.toMvPolynomial = _
  rw [Cubic.eval_toMvPolynomial]

/-- The universal coordinates are the affine line `T p + d` through the
normalized point, with `d` the universal projective line direction. -/
theorem kollar_universal_coordinate_decomposition
    {K : Type u} [Field K] :
    (fun i : Fin 4 => Fin.cases (Polynomial.X : (MvPolynomial (Fin 3) K)[X])
      (fun j : Fin 3 => Polynomial.C (MvPolynomial.X j)) i) =
      (Polynomial.X : (MvPolynomial (Fin 3) K)[X]) •
        (fun i => Polynomial.C (MvPolynomial.C (kollarBasePoint K i))) +
      1 • (fun i => Polynomial.C (kollarProjectiveLinePolynomialDirection K i)) := by
  rw [kollarProjectiveLinePolynomialDirection_eq_standard]
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [kollarBasePoint]
  · intro j
    rw [Fin.cases_succ]
    refine Fin.cases ?_ ?_ j
    · simp [kollarBasePoint]
    · intro k
      refine Fin.cases ?_ ?_ k
      · simp [kollarBasePoint]
      · intro h
        refine Fin.cases ?_ ?_ h
        · simp [kollarBasePoint]
        · intro z
          exact Fin.elim0 z

/-- In the universal coordinates, the cubic polynomial is its restriction to
Kollár's universal line through the normalized base point. -/
theorem kollar_finSucc_cubic_eq_universal_line_eval
    {K : Type u} [Field K] (c : Cubic K 4) :
    MvPolynomial.finSuccEquiv K 3 c.toMvPolynomial =
      (c.map ((Polynomial.C : MvPolynomial (Fin 3) K →+*
        (MvPolynomial (Fin 3) K)[X]).comp MvPolynomial.C)).eval
        ((Polynomial.X : (MvPolynomial (Fin 3) K)[X]) •
          (fun i => Polynomial.C (MvPolynomial.C (kollarBasePoint K i))) +
        1 • (fun i => Polynomial.C (kollarProjectiveLinePolynomialDirection K i))) := by
  rw [kollar_finSucc_cubic_eq_universal_eval]
  rw [kollar_universal_coordinate_decomposition]

theorem cubic_eval_polynomial_line
    {R : Type u} [CommRing R] (c : Cubic R 4)
    (p d : Fin 4 → R) :
    (c.map (Polynomial.C : R →+* R[X])).eval
      ((Polynomial.X : R[X]) • (fun i => Polynomial.C (p i)) +
        (1 : R[X]) • (fun i => Polynomial.C (d i))) =
      (Polynomial.X : R[X]) ^ 3 * Polynomial.C (c.eval p) +
        Polynomial.X ^ 2 * Polynomial.C (c.mixed p d) +
        Polynomial.X * Polynomial.C (c.mixed d p) +
        Polynomial.C (c.eval d) := by
  rw [Cubic.eval_line]
  simp only [one_pow, mul_one]
  rw [Cubic.eval_map, Cubic.mixed_map, Cubic.mixed_map, Cubic.eval_map]
  simp

theorem cubic_eval_polynomial_line_coeff_two
    {R : Type u} [CommRing R] (c : Cubic R 4)
    (p d : Fin 4 → R) :
    ((c.map (Polynomial.C : R →+* R[X])).eval
      ((Polynomial.X : R[X]) • (fun i => Polynomial.C (p i)) +
        (1 : R[X]) • (fun i => Polynomial.C (d i)))).coeff 2 =
      c.mixed p d := by
  rw [cubic_eval_polynomial_line]
  simp [Polynomial.coeff_C_mul]

theorem cubic_eval_polynomial_mixed_line_coeff_two
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (c : Cubic R 4)
    (p : Fin 4 → R) (d : Fin 4 → S) :
    ((c.map ((Polynomial.C : S →+* S[X]).comp f)).eval
      ((Polynomial.X : S[X]) •
          (fun i => Polynomial.C (f (p i))) +
        (1 : S[X]) • (fun i => Polynomial.C (d i)))).coeff 2 =
      (c.map f).mixed (fun i => f (p i)) d := by
  change ((((c.map f).map Polynomial.C).eval
    ((Polynomial.X : S[X]) •
        (fun i => Polynomial.C (f (p i))) +
      (1 : S[X]) • (fun i => Polynomial.C (d i)))).coeff 2) = _
  exact cubic_eval_polynomial_line_coeff_two (c.map f)
    (fun i => f (p i)) d

theorem cubic_polynomial_line_eq_reverse_residual_of_eval_zero
    {R : Type u} [CommRing R] [NoZeroDivisors R]
    (c : Cubic R 4) (p d : Fin 4 → R)
    (hp : c.eval p = 0) (hd : c.eval d ≠ 0) :
    (Polynomial.X : R[X]) ^ 3 * Polynomial.C (c.eval p) +
        Polynomial.X ^ 2 * Polynomial.C (c.mixed p d) +
        Polynomial.X * Polynomial.C (c.mixed d p) +
        Polynomial.C (c.eval d) =
      (Cubic.lineResidualPolynomial c p d).reverse := by
  rw [hp, map_zero, mul_zero, zero_add,
    kollar_reverse_lineResidualPolynomial c p d hd]
  ac_rfl

theorem kollarDistinguishedCoordinatePolynomial_eq_lineEvaluation
    {K : Type u} [Field K] (c : Cubic K 4) :
    kollarDistinguishedCoordinatePolynomial c =
      kollarUniversalLineEvaluationPolynomial c := by
  exact kollar_finSucc_cubic_eq_universal_line_eval c

noncomputable def kollarLastDirectionPolynomial
    {K : Type u} [Field K] (c : Cubic K 4) : K[X] :=
  (kollarDistinguishedCoordinatePolynomial c).map
    (MvPolynomial.eval (![0, 0, 1] : Fin 3 → K))

noncomputable def kollarSpecializedProjectiveLineDirection
    (K : Type u) [Field K] (a : Fin 3 → K) : Fin 4 → K :=
  fun i => MvPolynomial.eval a (kollarProjectiveLinePolynomialDirection K i)

noncomputable def kollarSpecializedDirectionPolynomial
    {K : Type u} [Field K] (c : Cubic K 4) (a : Fin 3 → K) : K[X] :=
  (kollarDistinguishedCoordinatePolynomial c).map (MvPolynomial.eval a)

noncomputable def kollarDirectionCubicValuePolynomial
    {K : Type u} [Field K] (c : Cubic K 4) :
    KollarProjectiveDirectionRing K :=
  (kollarProjectiveDirectionCubic c).eval
    (kollarProjectiveLinePolynomialDirection K)

noncomputable def kollarDirectionSecantPolynomial
    {K : Type u} [Field K] (c : Cubic K 4) :
    KollarProjectiveDirectionRing K :=
  (kollarProjectiveDirectionCubic c).mixed
    (kollarProjectiveDirectionBase K)
    (kollarProjectiveLinePolynomialDirection K)

theorem finCons_lastDirection_eq_line
    {K : Type u} [Field K] (t : K) :
    (Fin.cons t (![0, 0, 1] : Fin 3 → K) : Fin 4 → K) =
      t • kollarBasePoint K +
        kollarAffineLineDirection K (fun _ => 0) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [kollarBasePoint, kollarAffineLineDirection]
  · fin_cases j <;>
      simp [kollarBasePoint, kollarAffineLineDirection]

theorem finCons_eq_kollarSpecializedDirection_line
    {K : Type u} [Field K] (a : Fin 3 → K) (t : K) :
    (Fin.cons t a : Fin 4 → K) =
      t • kollarBasePoint K +
        kollarSpecializedProjectiveLineDirection K a := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [kollarBasePoint, kollarSpecializedProjectiveLineDirection,
      kollarProjectiveLinePolynomialDirection_eq_standard]
  · rw [Fin.cons_succ]
    fin_cases j <;>
      simp [kollarBasePoint, kollarSpecializedProjectiveLineDirection,
        kollarProjectiveLinePolynomialDirection_eq_standard]

theorem kollarLastDirectionPolynomial_eval
    {K : Type u} [Field K] (c : Cubic K 4) (t : K) :
    (kollarLastDirectionPolynomial c).eval t =
      c.eval (t • kollarBasePoint K +
        kollarAffineLineDirection K (fun _ => 0)) := by
  rw [kollarLastDirectionPolynomial, kollarDistinguishedCoordinatePolynomial,
    ← MvPolynomial.eval_eq_eval_mv_eval']
  rw [finCons_lastDirection_eq_line]
  change MvPolynomial.eval₂ (RingHom.id K)
    (t • kollarBasePoint K + kollarAffineLineDirection K (fun _ => 0))
      c.toMvPolynomial = _
  rw [Cubic.eval_toMvPolynomial]
  rfl

theorem kollarSpecializedDirectionPolynomial_eval
    {K : Type u} [Field K] (c : Cubic K 4)
    (a : Fin 3 → K) (t : K) :
    (kollarSpecializedDirectionPolynomial c a).eval t =
      c.eval (t • kollarBasePoint K +
        kollarSpecializedProjectiveLineDirection K a) := by
  rw [kollarSpecializedDirectionPolynomial,
    kollarDistinguishedCoordinatePolynomial,
    ← MvPolynomial.eval_eq_eval_mv_eval']
  rw [finCons_eq_kollarSpecializedDirection_line]
  change MvPolynomial.eval₂ (RingHom.id K)
    (t • kollarBasePoint K + kollarSpecializedProjectiveLineDirection K a)
      c.toMvPolynomial = _
  rw [Cubic.eval_toMvPolynomial]
  rfl

theorem kollarDirectionCubicValuePolynomial_eval
    {K : Type u} [Field K] (c : Cubic K 4) (a : Fin 3 → K) :
    MvPolynomial.eval a (kollarDirectionCubicValuePolynomial c) =
      c.eval (kollarSpecializedProjectiveLineDirection K a) := by
  let φ := MvPolynomial.eval₂Hom (RingHom.id K) a
  have h := Cubic.eval_map φ (kollarProjectiveDirectionCubic c)
    (kollarProjectiveLinePolynomialDirection K)
  have hc : (kollarProjectiveDirectionCubic c).map φ = c := by
    funext i
    simp [kollarProjectiveDirectionCubic, Cubic.map, φ]
  rw [hc] at h
  exact h.symm

theorem kollarDirectionSecantPolynomial_eval
    {K : Type u} [Field K] (c : Cubic K 4) (a : Fin 3 → K) :
    MvPolynomial.eval a (kollarDirectionSecantPolynomial c) =
      c.mixed (kollarBasePoint K)
        (kollarSpecializedProjectiveLineDirection K a) := by
  let φ := MvPolynomial.eval₂Hom (RingHom.id K) a
  have h := Cubic.mixed_map φ (kollarProjectiveDirectionCubic c)
    (kollarProjectiveDirectionBase K)
    (kollarProjectiveLinePolynomialDirection K)
  have hc : (kollarProjectiveDirectionCubic c).map φ = c := by
    funext i
    simp [kollarProjectiveDirectionCubic, Cubic.map, φ]
  have hp : (fun i => φ (kollarProjectiveDirectionBase K i)) =
      kollarBasePoint K := by
    funext i
    simp [kollarProjectiveDirectionBase, φ]
  rw [hc, hp] at h
  exact h.symm

theorem kollarDirectionSecantPolynomial_ne_zero
    {K : Type u} [Field K] (c : Cubic K 4)
    (hsec : c.mixed (kollarBasePoint K)
      (kollarAffineLineDirection K (fun _ => 0)) ≠ 0) :
    kollarDirectionSecantPolynomial c ≠ 0 := by
  exact kollar_projective_line_secantCoefficient_ne_zero c hsec

theorem kollarDirectionCubicValuePolynomial_ne_zero_of_irreducible
    {K : Type u} [Field K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (c : Cubic K 4) (hc : c.toMvPolynomial = F)
    (hirr : Irreducible F) :
    kollarDirectionCubicValuePolynomial c ≠ 0 := by
  let R := KollarProjectiveDirectionRing K
  let L := FractionRing R
  let φ : R →+* L := algebraMap R L
  let g : Fin 4 → K := kollarDirectionPlaneNormal K
  have hg : g 0 ≠ 0 := by
    simp [g, kollarDirectionPlaneNormal]
  have hF0 : F ≠ 0 := hirr.ne_zero
  have hprime : (Ideal.span ({F} : Set (MvPolynomial (Fin 4) K))).IsPrime :=
    principalIdeal_prime_of_irreducible_cubic F hirr
  have hrestF : rectangularSubstitution (hyperplaneInclusion g 0) F ≠ 0 :=
    hyperplane_restriction_ne_zero_of_prime F hF hF0 hprime g 0 hg
  have hrest : rectangularSubstitution (hyperplaneInclusion g 0)
      c.toMvPolynomial ≠ 0 := by
    rw [hc]
    exact hrestF
  have hd : kollarGenericProjectiveLineDirection K =
      genericHyperplaneDirection g 0 := by
    funext i
    simp only [kollarGenericProjectiveLineDirection,
      kollarProjectiveLinePolynomialDirection, genericHyperplaneDirection, g]
    rw [Matrix.mulVec, Matrix.mulVec]
    simp only [dotProduct]
    rw [_root_.map_sum]
    simp only [Matrix.map_apply, map_mul]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
  have hgeneric :
      (c.map (algebraMap K L)).eval
        (kollarGenericProjectiveLineDirection K) ≠ 0 := by
    rw [hd, cubic_eval_genericHyperplaneDirection]
    intro hzero
    apply hrest
    have hz : φ (rectangularSubstitution (hyperplaneInclusion g 0)
        c.toMvPolynomial) = φ 0 := by
      simpa only [map_zero] using hzero
    exact (IsFractionRing.injective R L) hz
  intro hzero
  apply hgeneric
  have hmap := Cubic.eval_map φ (kollarProjectiveDirectionCubic c)
    (kollarProjectiveLinePolynomialDirection K)
  have hcmap : (kollarProjectiveDirectionCubic c).map φ =
      c.map (algebraMap K L) := by
    funext i
    exact IsScalarTower.algebraMap_apply K R L (c i)
  change (kollarProjectiveDirectionCubic c).eval
    (kollarProjectiveLinePolynomialDirection K) = 0 at hzero
  rw [hcmap, hzero, map_zero] at hmap
  exact hmap

theorem kollarLastDirectionPolynomial_eq_cubicLinePolynomial
    {K : Type u} [Field K] [Infinite K] (c : Cubic K 4) :
    kollarLastDirectionPolynomial c =
      cubicLinePolynomial c (kollarBasePoint K)
        (kollarAffineLineDirection K (fun _ => 0)) := by
  apply Polynomial.funext
  intro t
  rw [kollarLastDirectionPolynomial_eval]
  have h := cubicLinePolynomial_eval₂ (RingHom.id K) c
    (kollarBasePoint K) (kollarAffineLineDirection K (fun _ => 0)) t
  have hc : c.map (RingHom.id K) = c := by
    funext i
    rfl
  rw [hc] at h
  exact h.symm

theorem kollarSpecializedDirectionPolynomial_eq_cubicLinePolynomial
    {K : Type u} [Field K] [Infinite K]
    (c : Cubic K 4) (a : Fin 3 → K) :
    kollarSpecializedDirectionPolynomial c a =
      cubicLinePolynomial c (kollarBasePoint K)
        (kollarSpecializedProjectiveLineDirection K a) := by
  apply Polynomial.funext
  intro t
  rw [kollarSpecializedDirectionPolynomial_eval]
  have h := cubicLinePolynomial_eval₂ (RingHom.id K) c
    (kollarBasePoint K) (kollarSpecializedProjectiveLineDirection K a) t
  have hc : c.map (RingHom.id K) = c := by
    funext i
    rfl
  rw [hc] at h
  exact h.symm

theorem kollarLastDirectionPolynomial_coeff_two
    {K : Type u} [Field K] [Infinite K] (c : Cubic K 4) :
    (kollarLastDirectionPolynomial c).coeff 2 =
      c.mixed (kollarBasePoint K)
        (kollarAffineLineDirection K (fun _ => 0)) := by
  rw [kollarLastDirectionPolynomial_eq_cubicLinePolynomial]
  simp [cubicLinePolynomial, Polynomial.coeff_C_mul]

theorem kollarLastDirectionPolynomial_coeff_three
    {K : Type u} [Field K] [Infinite K] (c : Cubic K 4) :
    (kollarLastDirectionPolynomial c).coeff 3 =
      c.eval (kollarBasePoint K) := by
  rw [kollarLastDirectionPolynomial_eq_cubicLinePolynomial]
  simp [cubicLinePolynomial, Polynomial.coeff_C_mul]

theorem kollarDistinguishedCoordinatePolynomial_coeff_three_eq_zero
    {K : Type u} [Field K] [Infinite K] (c : Cubic K 4)
    (hhom : c.toMvPolynomial.IsHomogeneous 3)
    (hpoint : c.eval (kollarBasePoint K) = 0) :
    (kollarDistinguishedCoordinatePolynomial c).coeff 3 = 0 := by
  let q := (kollarDistinguishedCoordinatePolynomial c).coeff 3
  have hqhom : q.IsHomogeneous 0 := by
    exact hhom.finSuccEquiv_coeff_isHomogeneous 3 0 (by omega)
  have hqC : q = MvPolynomial.C (MvPolynomial.coeff 0 q) := by
    exact MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
      ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 3)).mpr hqhom)
  have heval : MvPolynomial.eval (![0, 0, 1] : Fin 3 → K) q = 0 := by
    rw [← Polynomial.coeff_map]
    change (kollarLastDirectionPolynomial c).coeff 3 = 0
    rw [kollarLastDirectionPolynomial_coeff_three, hpoint]
  rw [hqC] at heval
  change q = 0
  rw [hqC]
  simpa using heval

theorem kollarDistinguishedCoordinatePolynomial_coeff_two_ne_zero
    {K : Type u} [Field K] [Infinite K] (c : Cubic K 4)
    (hsec : c.mixed (kollarBasePoint K)
      (kollarAffineLineDirection K (fun _ => 0)) ≠ 0) :
    (kollarDistinguishedCoordinatePolynomial c).coeff 2 ≠ 0 := by
  intro hzero
  apply hsec
  rw [← kollarLastDirectionPolynomial_coeff_two c]
  rw [kollarLastDirectionPolynomial, Polynomial.coeff_map, hzero, map_zero]

theorem kollarDistinguishedCoordinatePolynomial_natDegree_eq_two
    {K : Type u} [Field K] [Infinite K] (c : Cubic K 4)
    (hhom : c.toMvPolynomial.IsHomogeneous 3)
    (hpoint : c.eval (kollarBasePoint K) = 0)
    (hsec : c.mixed (kollarBasePoint K)
      (kollarAffineLineDirection K (fun _ => 0)) ≠ 0) :
    (kollarDistinguishedCoordinatePolynomial c).natDegree = 2 := by
  let P := kollarDistinguishedCoordinatePolynomial c
  have hF0 : c.toMvPolynomial ≠ 0 :=
    kollar_equation_ne_zero_of_secantCoefficient_ne_zero c hsec
  have hdegree : P.natDegree ≤ 3 := by
    change (MvPolynomial.finSuccEquiv K 3 c.toMvPolynomial).natDegree ≤ 3
    rw [MvPolynomial.natDegree_finSuccEquiv]
    calc
      MvPolynomial.degreeOf 0 c.toMvPolynomial ≤
          c.toMvPolynomial.totalDegree :=
        MvPolynomial.degreeOf_le_totalDegree _ _
      _ = 3 := hhom.totalDegree hF0
  have hcoeff2 : P.coeff 2 ≠ 0 :=
    kollarDistinguishedCoordinatePolynomial_coeff_two_ne_zero c hsec
  have hcoeff3 : P.coeff 3 = 0 :=
    kollarDistinguishedCoordinatePolynomial_coeff_three_eq_zero c hhom hpoint
  dsimp [P] at hdegree hcoeff2 hcoeff3 ⊢
  apply le_antisymm
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro m hm
    by_cases hm3 : m = 3
    · simpa [hm3] using hcoeff3
    · apply Polynomial.coeff_eq_zero_of_natDegree_lt
      omega
  · exact Polynomial.le_natDegree_of_ne_zero hcoeff2

/-- Irreducibility of the cubic equation passes, by the multivariable
coordinate equivalence and Gauss's lemma, to the distinguished-coordinate
polynomial over the generic-direction fraction field. -/
theorem kollarDistinguishedCoordinatePolynomial_generic_irreducible
    {K : Type u} [Field K] [Infinite K] (c : Cubic K 4)
    (hirr : Irreducible c.toMvPolynomial)
    (hsec : c.mixed (kollarBasePoint K)
      (kollarAffineLineDirection K (fun _ => 0)) ≠ 0) :
    Irreducible ((kollarDistinguishedCoordinatePolynomial c).map
      (algebraMap (KollarProjectiveDirectionRing K)
        (FractionRing (KollarProjectiveDirectionRing K)))) := by
  let P := kollarDistinguishedCoordinatePolynomial c
  have hPirr : Irreducible P := by
    exact hirr.map (MvPolynomial.finSuccEquiv K 3).toRingEquiv
  have hPdegree : P.natDegree ≠ 0 := by
    intro hdegree
    have hcoeff : P.coeff 2 = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      omega
    exact (kollarDistinguishedCoordinatePolynomial_coeff_two_ne_zero c hsec)
      hcoeff
  have hprimitive : P.IsPrimitive := hPirr.isPrimitive hPdegree
  exact hprimitive.irreducible_iff_irreducible_map_fraction_map.mp hPirr

theorem polynomial_discr_ne_zero_of_separable_of_pos_degree
    {K : Type u} [Field K] [CharZero K] (f : K[X])
    (hpos : 0 < f.degree) (hsep : f.Separable) :
    f.discr ≠ 0 := by
  have hf : f ≠ 0 := by
    intro h
    simp [h] at hpos
  have hcoprime : IsCoprime f f.derivative :=
    (Polynomial.separable_def f).mp hsep
  have hres : f.resultant f.derivative ≠ 0 := by
    intro hzero
    exact ((Polynomial.resultant_eq_zero_iff).mp hzero).2 hcoprime
  change Polynomial.resultant f f.derivative f.natDegree
    f.derivative.natDegree ≠ 0 at hres
  rw [Polynomial.natDegree_derivative,
    Polynomial.resultant_deriv hpos] at hres
  intro hdisc
  apply hres
  rw [hdisc, mul_zero]

theorem quadratic_discr_map_of_degree_two
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : R[X])
    (hf : f.degree = 2) (hmap : (f.map φ).degree = 2) :
    (f.map φ).discr = φ f.discr := by
  rw [Polynomial.discr_of_degree_eq_two hmap,
    Polynomial.discr_of_degree_eq_two hf]
  simp only [Polynomial.coeff_map, map_sub, map_pow, map_mul, map_ofNat]

/-- The generic-direction discriminant is a nonzero polynomial for a
normalized irreducible cubic with a nonzero selected first derivative. -/
theorem kollarDistinguishedCoordinatePolynomial_discr_ne_zero
    {K : Type u} [Field K] [CharZero K] [Infinite K]
    (c : Cubic K 4) (hhom : c.toMvPolynomial.IsHomogeneous 3)
    (hirr : Irreducible c.toMvPolynomial)
    (hpoint : c.eval (kollarBasePoint K) = 0)
    (hsec : c.mixed (kollarBasePoint K)
      (kollarAffineLineDirection K (fun _ => 0)) ≠ 0) :
    (kollarDistinguishedCoordinatePolynomial c).discr ≠ 0 := by
  let R := KollarProjectiveDirectionRing K
  let L := FractionRing R
  let P := kollarDistinguishedCoordinatePolynomial c
  let φ : R →+* L := algebraMap R L
  have hφ : Function.Injective φ := IsFractionRing.injective R L
  have hPnat : P.natDegree = 2 :=
    kollarDistinguishedCoordinatePolynomial_natDegree_eq_two
      c hhom hpoint hsec
  have hPdegree : P.degree = 2 := by
    apply (Polynomial.degree_eq_iff_natDegree_eq_of_pos
      (by decide : 0 < 2)).mpr
    exact hPnat
  have hmapDegree : (P.map φ).degree = 2 := by
    rw [Polynomial.degree_map_eq_of_injective hφ]
    exact hPdegree
  have hmapIrr : Irreducible (P.map φ) :=
    kollarDistinguishedCoordinatePolynomial_generic_irreducible
      c hirr hsec
  have hmapDisc : (P.map φ).discr ≠ 0 :=
    polynomial_discr_ne_zero_of_separable_of_pos_degree (P.map φ)
      (by rw [hmapDegree]; decide) hmapIrr.separable
  intro hzero
  apply hmapDisc
  rw [quadratic_discr_map_of_degree_two φ P hPdegree hmapDegree,
    hzero, map_zero]

end AllCharacteristics
