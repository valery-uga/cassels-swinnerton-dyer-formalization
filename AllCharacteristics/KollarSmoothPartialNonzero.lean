import AllCharacteristics.KollarThreeFormsCommonZero
import AllCharacteristics.SmoothCubicJacobianProjectiveEmpty
import PfaffianDescent.VoisinProjectiveVectorSchemePoint

/-! Kollár §18 for smooth cubic surfaces. In characteristic different from three,
a zero partial gives three quadrics with a nonzero common geometric zero.
Euler's identity puts it on the cubic; the resulting actual Jacobian scheme
point contradicts smoothness. No inverse Frobenius or perfectness is used.
-/

noncomputable section
namespace AllCharacteristics
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousProjective PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Euler converts simultaneous vanishing of all partials into vanishing of
the equation when the cubic degree is nonzero in the coefficient field. -/
theorem cubic_eval_eq_zero_of_all_pderiv_eval_eq_zero
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (h3 : (3 : K) ≠ 0) (x : Fin 4 → K)
    (hx : ∀ i : Fin 4, (pderiv i p).eval x = 0) :
    p.eval x = 0 := by
  have he : (3 : K) * p.eval x = 0 := by
    calc
      (3 : K) * p.eval x = MvPolynomial.eval x (3 • p) := by
        simp [nsmul_eq_mul]
      _ = MvPolynomial.eval x (∑ i : Fin 4, X i * pderiv i p) :=
        congrArg (MvPolynomial.eval x) hp.sum_X_mul_pderiv.symm
      _ = 0 := by simp [hx]
  exact (mul_eq_zero.mp he).resolve_left h3

/-- A nonzero vector with vanishing equation and partials produces a point
of the actual cubic Jacobian scheme, including its original equation. -/
theorem nonempty_cubicJacobianScheme_of_nonzero_singular_vector
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (x : Fin 4 → K) (hx0 : x ≠ 0) (hpzero : p.eval x = 0)
    (hx : ∀ i : Fin 4, (pderiv i p).eval x = 0) :
    Nonempty (scheme (cubicJacobianIdeal p hp)) := by
  let e := MvPolynomial.eval₂Hom (RingHom.id K) x
  have hle : (cubicJacobianIdeal p hp).toIdeal ≤ RingHom.ker e := by
    simp only [cubicJacobianIdeal, HomogeneousIdeal.toIdeal_sup,
      HomogeneousIdeal.toIdeal_iSup, sup_le_iff, iSup_le_iff]
    change (Ideal.span {p} ≤ RingHom.ker e ∧
      ∀ j : Fin 4, Ideal.span {pderiv j p} ≤ RingHom.ker e)
    constructor
    · apply Ideal.span_le.mpr
      rintro z rfl
      exact hpzero
    · intro j
      apply Ideal.span_le.mpr
      rintro z rfl
      exact hx j
  have hvan : ∀ q ∈ (cubicJacobianIdeal p hp).toIdeal, q.eval x = 0 := by
    intro q hq
    exact hle hq
  obtain ⟨t, _⟩ := exists_projectiveVectorSchemePoint_of_nonzero_zero
    (cubicJacobianIdeal p hp) x hx0 hvan
  exact ⟨t (default : Spec (.of K))⟩

/-- Over an algebraically closed field of characteristic different from
three, no partial of a nonzero smooth cubic surface can be identically zero.
This includes characteristic two. -/
theorem smoothCubic_pderiv_zero_ne_zero_of_algClosed
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (h3 : (3 : K) ≠ 0) [Smooth (hypersurfaceToBase p hp)] :
    pderiv 0 p ≠ 0 := by
  intro hzero
  obtain ⟨x, hx0, h1, h2, h3x⟩ :=
    exists_nonzero_common_zero_three_of_homogeneous_pos
      (pderiv 1 p) (pderiv 2 p) (pderiv 3 p)
      hp.pderiv hp.pderiv hp.pderiv (by decide) (by decide) (by decide)
  have hpartial : ∀ i : Fin 4, (pderiv i p).eval x = 0 := by
    intro i
    by_cases hi0 : i = 0
    · rw [hi0, hzero, map_zero]
    by_cases hi1 : i = 1
    · rw [hi1]
      simpa only [MvPolynomial.aeval_def, Algebra.algebraMap_self,
        MvPolynomial.eval₂_id] using h1
    by_cases hi2 : i = 2
    · rw [hi2]
      simpa only [MvPolynomial.aeval_def, Algebra.algebraMap_self,
        MvPolynomial.eval₂_id] using h2
    have hi3 : i = 3 := by omega
    rw [hi3]
    simpa only [MvPolynomial.aeval_def, Algebra.algebraMap_self,
      MvPolynomial.eval₂_id] using h3x
  have hpzero := cubic_eval_eq_zero_of_all_pderiv_eval_eq_zero p hp h3 x hpartial
  obtain ⟨z⟩ := nonempty_cubicJacobianScheme_of_nonzero_singular_vector
    p hp x hx0 hpzero hpartial
  letI := smoothCubic_cubicJacobianScheme_isEmpty p hp hp0
  exact isEmptyElim z

/-- The preceding conclusion over an arbitrary, possibly imperfect, field.
The common zero is only sought after coefficient extension to an algebraic
closure, where smoothness is preserved by actual scheme base change. -/
theorem smoothCubic_pderiv_zero_ne_zero_of_three_ne_zero
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (h3 : (3 : K) ≠ 0) [Smooth (hypersurfaceToBase p hp)] :
    pderiv 0 p ≠ 0 := by
  let L : Type u := AlgebraicClosure K
  let f : K →+* L := algebraMap K L
  have hf : Function.Injective f := FaithfulSMul.algebraMap_injective K L
  have hmapinj : Function.Injective (MvPolynomial.map f :
      MvPolynomial (Fin 4) K → MvPolynomial (Fin 4) L) :=
    MvPolynomial.map_injective f hf
  have hmap0 : p.map f ≠ 0 := by
    intro h
    exact hp0 (hmapinj (by simpa using h))
  have h3L : (3 : L) ≠ 0 := by
    intro h
    apply h3
    apply hf
    simpa only [map_ofNat, map_zero] using h
  letI : Smooth (hypersurfaceToBase (p.map f) (hp.map f)) :=
    smooth_hypersurfaceToBase_map f p hp
  have hnz := smoothCubic_pderiv_zero_ne_zero_of_algClosed
    (p.map f) (hp.map f) hmap0 h3L
  intro hzero
  apply hnz
  rw [MvPolynomial.pderiv_map, hzero, map_zero]

end AllCharacteristics
