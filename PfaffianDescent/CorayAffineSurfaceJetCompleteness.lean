import PfaffianDescent.CorayAffinePointSquareTaylor
import PfaffianDescent.CubicClosedPointSerreSurfaceJetsTaylor
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Completeness of the normalized two-direction affine surface jet

At an actual affine hypersurface point over a field, a nonzero Jacobian pivot
constructs the two free tangent directions. Vanishing of this actual full jet
forces a polynomial into the point-ideal square modulo the surface equation.
There is no supplied square-membership or cotangent-isomorphism certificate.

STATUS: UNVERIFIED source draft. Root owns all compiler checks.
-/

noncomputable section
namespace PfaffianDescent.Coray

open MvPolynomial TrivSqZeroExt

universe u
variable {M : Type u} [Field M]

/-- The canonical two free directions determined by a Jacobian pivot. -/
def affineNormalizedSurfaceRows (a : Fin 3 → M) (pivot : Fin 3) :
    Fin 3 → Fin 2 → M :=
  Fin.insertNth pivot (fun t => -a (pivot.succAbove t) / a pivot)
    (fun t => Pi.single t 1)

/-- The explicitly constructed rows annihilate the actual gradient. -/
theorem affineNormalizedSurfaceRows_gradient_zero
    (a : Fin 3 → M) (pivot : Fin 3) (ha : a pivot ≠ 0) :
    ∑ i, a i • affineNormalizedSurfaceRows a pivot i = 0 := by
  classical
  rw [Fin.sum_univ_succAbove _ pivot]
  funext t
  simp [affineNormalizedSurfaceRows, Finset.sum_apply, Pi.single_apply,
    Pi.smul_apply, smul_eq_mul]
  field_simp [ha]
  fin_cases t <;> simp

/-- The annihilator of the two canonical directions is exactly the span of
the gradient, proved directly using the nonzero pivot. -/
theorem affineNormalizedSurfaceRows_annihilator
    (a b : Fin 3 → M) (pivot : Fin 3) (ha : a pivot ≠ 0)
    (hb : ∑ i, b i • affineNormalizedSurfaceRows a pivot i = 0) :
    ∀ i, b i = (b pivot / a pivot) * a i := by
  classical
  intro i
  by_cases hi : i = pivot
  · subst i
    exact (div_mul_cancel₀ (b pivot) ha).symm
  · obtain ⟨t, rfl⟩ := Fin.exists_succAbove_eq hi
    rw [Fin.sum_univ_succAbove _ pivot] at hb
    have ht := congrFun hb t
    simp [affineNormalizedSurfaceRows, Finset.sum_apply, Pi.single_apply,
      Pi.smul_apply, smul_eq_mul, mul_ite] at ht
    apply sub_eq_zero.mp
    calc
      b (pivot.succAbove t) - (b pivot / a pivot) * a (pivot.succAbove t) =
          b pivot * (-a (pivot.succAbove t) / a pivot) + b (pivot.succAbove t) := by ring
      _ = 0 := by
        fin_cases t <;> simpa using ht

/-- The actual polynomial evaluation coordinates of the normalized full jet. -/
def affineNormalizedSurfaceJetCoordinates
    (p : MvPolynomial (Fin 3) M) (x : Fin 3 → M) (pivot : Fin 3) :
    Fin 3 → CubicSurfaceFirstJet M :=
  fun i => inl (x i) +
    inr (affineNormalizedSurfaceRows (fun j => eval x (pderiv j p)) pivot i)

/-- The normalized jet lies on the actual hypersurface. -/
theorem affineNormalizedSurfaceJetCoordinates_equation_zero
    (p : MvPolynomial (Fin 3) M) (x : Fin 3 → M) (pivot : Fin 3)
    (hp : eval x p = 0) (hpivot : eval x (pderiv pivot p) ≠ 0) :
    aeval (affineNormalizedSurfaceJetCoordinates p x pivot) p = 0 := by
  unfold affineNormalizedSurfaceJetCoordinates
  rw [cubicClosedPointSerreSurfaceJets_taylor]
  change inl (eval x p) +
    inr (∑ i, eval x (pderiv i p) •
      affineNormalizedSurfaceRows (fun j => eval x (pderiv j p)) pivot i) = 0
  rw [hp, affineNormalizedSurfaceRows_gradient_zero _ pivot hpivot]
  simp

/-- Full-jet vanishing forces all ambient first-order coefficients to be
proportional to those of the surface equation, rather than assuming that fact. -/
theorem affineNormalizedSurfaceJet_zero_value_and_proportional_partials
    (p q : MvPolynomial (Fin 3) M) (x : Fin 3 → M) (pivot : Fin 3)
    (hpivot : eval x (pderiv pivot p) ≠ 0)
    (hq : aeval (affineNormalizedSurfaceJetCoordinates p x pivot) q = 0) :
    eval x q = 0 ∧
      (∀ i, eval x (pderiv i q) =
        (eval x (pderiv pivot q) / eval x (pderiv pivot p)) *
          eval x (pderiv i p)) := by
  have ht := cubicClosedPointSerreSurfaceJets_taylor x
    (affineNormalizedSurfaceRows (fun j => eval x (pderiv j p)) pivot) q
  change aeval (affineNormalizedSurfaceJetCoordinates p x pivot) q =
    inl (eval x q) + inr (∑ i, eval x (pderiv i q) •
      affineNormalizedSurfaceRows (fun j => eval x (pderiv j p)) pivot i) at ht
  rw [hq] at ht
  have hvalue := congrArg TrivSqZeroExt.fst ht
  have hpartials := congrArg TrivSqZeroExt.snd ht
  refine ⟨by simpa using hvalue.symm, ?_⟩
  apply affineNormalizedSurfaceRows_annihilator _ _ pivot hpivot
  simpa using hpartials.symm

/-- The actual full jet supplies a concrete scalar multiple of the surface
equation whose subtraction lies in the actual ambient point-ideal square. -/
theorem affineNormalizedSurfaceJet_zero_sub_equation_mem_square
    (p q : MvPolynomial (Fin 3) M) (x : Fin 3 → M) (pivot : Fin 3)
    (hp : eval x p = 0) (hpivot : eval x (pderiv pivot p) ≠ 0)
    (hq : aeval (affineNormalizedSurfaceJetCoordinates p x pivot) q = 0) :
    q - C (eval x (pderiv pivot q) / eval x (pderiv pivot p)) * p ∈
      affinePointIdeal x ^ 2 := by
  obtain ⟨hvalue, hpartials⟩ :=
    affineNormalizedSurfaceJet_zero_value_and_proportional_partials p q x pivot hpivot hq
  apply affinePoint_mem_square_of_value_and_partials_zero
  · simp [hvalue, hp]
  · intro i
    simp only [map_sub, pderiv_C_mul, map_mul, MvPolynomial.eval_C,
      hpartials i, sub_self]

/-- Therefore the actual jet kernel is contained in the point-ideal square
plus the actual principal surface equation ideal. -/
theorem affineNormalizedSurfaceJet_zero_mem_square_sup_equation
    (p q : MvPolynomial (Fin 3) M) (x : Fin 3 → M) (pivot : Fin 3)
    (hp : eval x p = 0) (hpivot : eval x (pderiv pivot p) ≠ 0)
    (hq : aeval (affineNormalizedSurfaceJetCoordinates p x pivot) q = 0) :
    q ∈ affinePointIdeal x ^ 2 ⊔ Ideal.span ({p} : Set (MvPolynomial (Fin 3) M)) := by
  let c := eval x (pderiv pivot q) / eval x (pderiv pivot p)
  have hsquare : q - C c * p ∈ affinePointIdeal x ^ 2 :=
    affineNormalizedSurfaceJet_zero_sub_equation_mem_square p q x pivot hp hpivot hq
  have hequation : C c * p ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 3) M)) :=
    Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton p))
  have hsum := (affinePointIdeal x ^ 2 ⊔
    Ideal.span ({p} : Set (MvPolynomial (Fin 3) M))).add_mem
      (Submodule.mem_sup_left hsquare) (Submodule.mem_sup_right hequation)
  have heq : (q - C c * p) + C c * p = q := by ring
  rwa [heq] at hsum

/-- On the literal affine hypersurface quotient, the selected equation is
in the square of the actual image point ideal. -/
theorem affineNormalizedSurfaceJet_zero_mem_surface_point_square
    (p q : MvPolynomial (Fin 3) M) (x : Fin 3 → M) (pivot : Fin 3)
    (hp : eval x p = 0) (hpivot : eval x (pderiv pivot p) ≠ 0)
    (hq : aeval (affineNormalizedSurfaceJetCoordinates p x pivot) q = 0) :
    Ideal.Quotient.mk (Ideal.span ({p} : Set (MvPolynomial (Fin 3) M))) q ∈
      ((affinePointIdeal x).map
        (Ideal.Quotient.mk (Ideal.span ({p} : Set (MvPolynomial (Fin 3) M))))) ^ 2 := by
  let c := eval x (pderiv pivot q) / eval x (pderiv pivot p)
  let π := Ideal.Quotient.mk (Ideal.span ({p} : Set (MvPolynomial (Fin 3) M)))
  have hsquare : q - C c * p ∈ affinePointIdeal x ^ 2 :=
    affineNormalizedSurfaceJet_zero_sub_equation_mem_square p q x pivot hp hpivot hq
  have hmap : π (q - C c * p) ∈ (affinePointIdeal x ^ 2).map π :=
    Ideal.mem_map_of_mem π hsquare
  have hpzero : π p = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton p))
  rw [Ideal.map_pow] at hmap
  simpa only [map_sub, map_mul, hpzero, mul_zero, sub_zero] using hmap

end PfaffianDescent.Coray
