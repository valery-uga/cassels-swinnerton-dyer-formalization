import AllCharacteristics.CubicSmoothing
import AllCharacteristics.CubicTranslationDirection
import PfaffianDescent.MultivariateCubic
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# The smooth/double/triple trichotomy for a cubic point

For an ordered cubic tensor, restriction to the line through vectors `a` and
`v` has coefficients `eval a`, `mixed a v`, `mixed v a`, and `eval v`.
These coefficients give a characteristic-free multiplicity trichotomy.  The
quadratic mixed coefficient is reconstructed from its values at the four
basis vectors and their six pairwise sums, so the argument remains valid over
finite fields, including `𝔽₂`.
-/

open scoped BigOperators
namespace AllCharacteristics
open PfaffianDescent

universe u

namespace Cubic

variable {R : Type u} [CommRing R] {n : ℕ}

/-- The quadratic dependence of `mixed a v` on its first argument, presented
as the diagonal of a bilinear map.  This works without dividing by two. -/
noncomputable def mixedLeftBilin (c : Cubic R n) (v : Fin n → R) :
    LinearMap.BilinMap R (Fin n → R) R :=
  LinearMap.mk₂ R
    (fun a b ↦ ∑ i, c i * (a i.1 * b i.2.1 * v i.2.2 +
      a i.1 * v i.2.1 * b i.2.2 + v i.1 * a i.2.1 * b i.2.2))
    (by
      intros
      simp only [Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring)
    (by
      intros
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring)
    (by
      intros
      simp only [Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring)
    (by
      intros
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring)

@[simp] theorem mixedLeftBilin_self (c : Cubic R n) (v a : Fin n → R) :
    mixedLeftBilin c v a a = c.mixed a v := by
  simp only [mixedLeftBilin, LinearMap.mk₂_apply, PfaffianDescent.Cubic.mixed]

/-- The quadratic map whose value at `a` is `mixed a v`. -/
noncomputable def mixedLeftQuadratic (c : Cubic R n) (v : Fin n → R) :
    QuadraticMap R (Fin n → R) R := (mixedLeftBilin c v).toQuadraticMap

@[simp] theorem mixedLeftQuadratic_apply (c : Cubic R n) (v a : Fin n → R) :
    mixedLeftQuadratic c v a = c.mixed a v := by
  simp [mixedLeftQuadratic]

/-- The linear dependence of `mixed v a` on its second argument. -/
noncomputable def mixedRightLinear (c : Cubic R n) (v : Fin n → R) :
    (Fin n → R) →ₗ[R] R where
  toFun a := c.mixed v a
  map_add' a b := by
    simp only [PfaffianDescent.Cubic.mixed, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  map_smul' t a := by
    simp only [PfaffianDescent.Cubic.mixed, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro i _
    ring

@[simp] theorem mixedRightLinear_apply (c : Cubic R n) (v a : Fin n → R) :
    mixedRightLinear c v a = c.mixed v a := rfl

variable {K : Type u} [Field K]

/-- Vanishing of the quadratic mixed coefficient on the ground field remains
an identity after every change of coefficient ring. -/
theorem mixed_left_map_eq_zero
    (c : Cubic K n) (v : Fin n → K)
    (h : ∀ a : Fin n → K, c.mixed a v = 0)
    {S : Type u} [CommRing S] (f : K →+* S) (a : Fin n → S) :
    (c.map f).mixed a (fun i ↦ f (v i)) = 0 := by
  classical
  let vf : Fin n → S := fun i ↦ f (v i)
  let Q := mixedLeftQuadratic (c.map f) vf
  have hmap (x : Fin n → K) : Q (fun i ↦ f (x i)) = 0 := by
    rw [mixedLeftQuadratic_apply, PfaffianDescent.Cubic.mixed_map, h, map_zero]
  have hb (i : Fin n) : Q (Pi.single i 1) = 0 := by
    have heq : (fun l ↦ f ((Pi.single i 1 : Fin n → K) l)) =
        (Pi.single i 1 : Fin n → S) := by
      funext l
      by_cases hli : l = i <;> simp [hli]
    rw [← heq]
    exact hmap (Pi.single i 1)
  have hp (i j : Fin n) : QuadraticMap.polar Q (Pi.single i 1) (Pi.single j 1) = 0 := by
    rw [QuadraticMap.polar]
    have hij := hmap (Pi.single i 1 + Pi.single j 1)
    have heq :
        (fun l ↦ f ((Pi.single i 1 : Fin n → K) l +
          (Pi.single j 1 : Fin n → K) l)) =
          ((Pi.single i 1 : Fin n → S) + Pi.single j 1) := by
      funext l
      by_cases hli : l = i <;> by_cases hlj : l = j <;>
        simp [Pi.single_apply, hli, hlj]
    have hij' : Q (fun l ↦ f ((Pi.single i 1 : Fin n → K) l +
        (Pi.single j 1 : Fin n → K) l)) = 0 := by
      simpa only [Pi.add_apply] using hij
    rw [← heq, hij', hb i, hb j]
    simp
  have hs (i : Fin n) : Q (a i • Pi.single i 1) = 0 := by
    rw [Q.map_smul, hb i, smul_zero]
  have hps (i j : Fin n) :
      QuadraticMap.polar Q (a i • Pi.single i 1) (a j • Pi.single j 1) = 0 := by
    rw [QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hp i j,
      smul_zero, smul_zero]
  rw [← mixedLeftQuadratic_apply]
  change Q a = 0
  nth_rw 1 [pi_eq_sum_univ' a]
  rw [Q.map_sum]
  simp only [hs, Finset.sum_const_zero, zero_add]
  apply Finset.sum_eq_zero
  intro ij _
  induction ij using Sym2.inductionOn with
  | _ i j => simpa only [Sym2.map_mk, QuadraticMap.polarSym2_sym2Mk] using hps i j

/-- Vanishing of the linear mixed coefficient also remains an identity after
every coefficient extension. -/
theorem mixed_right_map_eq_zero
    (c : Cubic K n) (v : Fin n → K)
    (h : ∀ a : Fin n → K, c.mixed v a = 0)
    {S : Type u} [CommRing S] (f : K →+* S) (a : Fin n → S) :
    (c.map f).mixed (fun i ↦ f (v i)) a = 0 := by
  classical
  let vf : Fin n → S := fun i ↦ f (v i)
  let L := mixedRightLinear (c.map f) vf
  have hmap (x : Fin n → K) : L (fun i ↦ f (x i)) = 0 := by
    rw [mixedRightLinear_apply, PfaffianDescent.Cubic.mixed_map, h, map_zero]
  have hb (i : Fin n) : L (Pi.single i 1) = 0 := by
    have heq : (fun l ↦ f ((Pi.single i 1 : Fin n → K) l)) =
        (Pi.single i 1 : Fin n → S) := by
      funext l
      by_cases hli : l = i <;> simp [hli]
    rw [← heq]
    exact hmap (Pi.single i 1)
  rw [← mixedRightLinear_apply]
  change L a = 0
  nth_rw 1 [pi_eq_sum_univ' a]
  rw [map_sum]
  simp only [map_smul, hb, smul_zero, Finset.sum_const_zero]

/-- The first mixed coefficient is the directional derivative of the cubic. -/
theorem mixed_eq_sum_pderiv_eval
    {A : Type u} [CommRing A] (c : Cubic A n) (x v : Fin n → A) :
    c.mixed x v = ∑ i, v i * (MvPolynomial.pderiv i c.toMvPolynomial).eval x := by
  classical
  simp only [PfaffianDescent.Cubic.mixed, PfaffianDescent.Cubic.toMvPolynomial,
    map_sum, MvPolynomial.pderiv_C, Derivation.leibniz,
    MvPolynomial.pderiv_X, MvPolynomial.eval_sum, MvPolynomial.eval_add,
    MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    Finset.mul_sum, Pi.single_apply, smul_eq_mul, mul_one, mul_zero, add_zero,
    zero_add, map_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  rintro ⟨i, j, k⟩ -
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp
  ring

/-- Evaluating the quadratic mixed coefficient at polynomial coordinates is
exactly the directional-derivative polynomial. -/
theorem mixed_polynomial_eq_directionalDerivative
    {A : Type u} [CommRing A] (c : Cubic A n) (v : Fin n → A) :
    (c.map MvPolynomial.C).mixed MvPolynomial.X (fun i ↦ MvPolynomial.C (v i)) =
      directionalDerivative c.toMvPolynomial v := by
  rw [mixed_eq_sum_pderiv_eval]
  simp only [directionalDerivative]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp only [PfaffianDescent.Cubic.toMvPolynomial, map_sum, Derivation.leibniz,
    MvPolynomial.pderiv_C, MvPolynomial.pderiv_X, smul_eq_mul, mul_zero, add_zero,
    MvPolynomial.eval_sum, MvPolynomial.eval_add, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X, Pi.single_apply]
  simp [PfaffianDescent.Cubic.map]

/-- A nonzero mixed coefficient makes the point a smooth coordinate point. -/
theorem isSmoothCoordinatePoint_of_mixed_ne_zero
    (c : Cubic K 4) (v d : Fin 4 → K)
    (hv : v ≠ 0) (heval : c.eval v = 0) (hmix : c.mixed v d ≠ 0) :
    IsSmoothCubicCoordinatePoint c.toMvPolynomial v := by
  refine ⟨hv, ?_, ?_⟩
  · simpa only [MvPolynomial.eval₂_id] using
      (PfaffianDescent.Cubic.eval_toMvPolynomial (RingHom.id K) c v).trans heval
  · have hsum : ∑ i, d i * (MvPolynomial.pderiv i c.toMvPolynomial).eval v ≠ 0 := by
      rwa [← mixed_eq_sum_pderiv_eval]
    by_contra hn
    push Not at hn
    apply hsum
    simp only [hn, mul_zero, Finset.sum_const_zero]

/-- Expanding the double-point coefficient after moving along the vertex
direction. -/
theorem mixed_add_smul_left (c : Cubic K 4) (a v : Fin 4 → K) (t : K) :
    c.mixed (a + t • v) v = c.mixed a v +
      (2 : K) * t * c.mixed v a + (3 : K) * t ^ 2 * c.eval v := by
  simp only [PfaffianDescent.Cubic.mixed, PfaffianDescent.Cubic.eval,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fintype.sum_prod_type,
    Fin.sum_univ_succ, Fin.sum_univ_zero]
  ring

/-- Projection from a double point produces a smooth point over the same
field. -/
theorem exists_smoothCoordinatePoint_of_double_mixed
    (c : Cubic K 4) (v : Fin 4 → K)
    (heval : c.eval v = 0)
    (hgrad : ∀ a : Fin 4 → K, c.mixed v a = 0)
    {a : Fin 4 → K} (ha : c.mixed a v ≠ 0) :
    ∃ q : Fin 4 → K, IsSmoothCubicCoordinatePoint c.toMvPolynomial q := by
  let t : K := -(c.eval a / c.mixed a v)
  let q : Fin 4 → K := a + t • v
  have hqeval : c.eval q = 0 := by
    dsimp only [q]
    have hline := c.eval_line a v 1 t
    simp only [one_smul, one_pow, one_mul] at hline
    rw [hgrad a, heval, mul_zero, add_zero] at hline
    rw [hline]
    dsimp only [t]
    field_simp
    ring
  have hqmix : c.mixed q v = c.mixed a v := by
    dsimp only [q]
    rw [mixed_add_smul_left, hgrad a, heval, mul_zero, add_zero]
    ring
  have hq0 : q ≠ 0 := by
    intro hzero
    apply ha
    rw [← hqmix, hzero]
    simp [PfaffianDescent.Cubic.mixed]
  exact ⟨q, isSmoothCoordinatePoint_of_mixed_ne_zero c q v hq0 hqeval
    (hqmix.symm ▸ ha)⟩

/-- If both mixed coefficients vanish, the vector is a translation direction
as a polynomial identity over every coefficient extension. -/
theorem isTranslationDirection_toMvPolynomial
    (c : Cubic K 4) (v : Fin 4 → K)
    (heval : c.eval v = 0)
    (hleft : ∀ a : Fin 4 → K, c.mixed a v = 0)
    (hright : ∀ a : Fin 4 → K, c.mixed v a = 0) :
    IsTranslationDirection c.toMvPolynomial v := by
  intro S _ f x s
  let vf : Fin 4 → S := fun i ↦ f (v i)
  rw [PfaffianDescent.Cubic.eval_toMvPolynomial,
    PfaffianDescent.Cubic.eval_toMvPolynomial]
  change (c.map f).eval (fun i ↦ x i + s * vf i) = (c.map f).eval x
  have hline := (c.map f).eval_line x vf 1 s
  have hL : (c.map f).mixed x vf = 0 := mixed_left_map_eq_zero c v hleft f x
  have hR : (c.map f).mixed vf x = 0 := mixed_right_map_eq_zero c v hright f x
  have hV : (c.map f).eval vf = 0 := by
    rw [show (c.map f).eval vf = f (c.eval v) from
      PfaffianDescent.Cubic.eval_map f c v]
    rw [heval, map_zero]
  have hvec : x + s • vf = fun i ↦ x i + s * vf i := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [one_smul, hvec] at hline
  simpa only [vf, one_mul, one_pow, hL, hR, hV, mul_zero, add_zero] using hline

end Cubic
end AllCharacteristics
