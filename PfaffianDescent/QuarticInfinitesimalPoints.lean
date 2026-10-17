import PfaffianDescent.QuarticSquareZeroQuotient
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.FieldTheory.Minpoly.Basic

/-!
# Affine first jets for the degree-four construction

This realizes a nonzero tangent vector at an affine point of a cubic as an
actual dual-number closed subscheme.  It is the geometric ingredient needed
to turn the rank-eight square-zero quotient into the finite subscheme used in
Proposition 4.3 of `2-proofs.tex`.
-/

namespace PfaffianDescent
namespace QuarticNet

open AlgebraicGeometry TrivSqZeroExt MvPolynomial

universe u

abbrev AffineThreeRing (k : Type u) [CommSemiring k] := MvPolynomial (Fin 3) k

section DualSurjectivity

variable {k L A : Type u} [Field k] [Field L] [Algebra k L]
  [CommRing A] [Algebra k A]

theorem polynomial_aeval_dual (P : Polynomial k) (a b : L) :
    Polynomial.aeval (TrivSqZeroExt.inl a + TrivSqZeroExt.inr b : DualNumber L) P =
      TrivSqZeroExt.inl (Polynomial.aeval a P) +
        TrivSqZeroExt.inr (Polynomial.aeval a P.derivative * b) := by
  have hb (Q : Polynomial k) :
      Polynomial.aeval (TrivSqZeroExt.inl a : DualNumber L) Q =
        TrivSqZeroExt.inl (Polynomial.aeval a Q) :=
    Polynomial.aeval_algHom_apply (TrivSqZeroExt.inlAlgHom k L L) a Q
  have hsq : (TrivSqZeroExt.inr b : DualNumber L) ^ 2 = 0 := by simp [pow_two]
  have h := Polynomial.eval_add_of_sq_eq_zero
    (P.map (algebraMap k (DualNumber L))) (TrivSqZeroExt.inl a) (TrivSqZeroExt.inr b) hsq
  simp only [← Polynomial.eval_map_algebraMap, Polynomial.derivative_map] at hb ⊢
  rw [h, Polynomial.derivative_map, hb, hb]
  congr 1
  apply TrivSqZeroExt.ext <;> simp [DualNumber.snd_mul, mul_comm]

theorem polynomial_aeval_dual_fst (P : Polynomial k) (x : DualNumber L) :
    (Polynomial.aeval x P).fst = Polynomial.aeval x.fst P := by
  have h := polynomial_aeval_dual P x.fst x.snd
  rw [TrivSqZeroExt.inl_fst_add_inr_snd_eq] at h
  rw [h]
  simp

theorem polynomial_aeval_dual_snd (P : Polynomial k) (x : DualNumber L) :
    (Polynomial.aeval x P).snd = Polynomial.aeval x.fst P.derivative * x.snd := by
  have h := polynomial_aeval_dual P x.fst x.snd
  rw [TrivSqZeroExt.inl_fst_add_inr_snd_eq] at h
  rw [h]
  simp

/-- A map to dual numbers is surjective once its residue map is surjective
and it has a nonzero infinitesimal direction. -/
theorem dualNumber_surjective_of_residue_and_nilpotent (h : A →ₐ[k] DualNumber L)
    (hres : Function.Surjective (fun a => (h a).fst))
    (hnil : ∃ n, (h n).fst = 0 ∧ (h n).snd ≠ 0) : Function.Surjective h := by
  obtain ⟨n, hn0, hn1⟩ := hnil
  intro x
  obtain ⟨a, ha⟩ := hres x.fst
  obtain ⟨c, hc⟩ := hres ((x.snd - (h a).snd) / (h n).snd)
  refine ⟨a + c * n, ?_⟩
  apply TrivSqZeroExt.ext
  · simp [ha, hn0]
  · simp only [map_add, map_mul, snd_add, DualNumber.snd_mul, hn0, mul_zero,
      add_zero, hc, div_mul_cancel₀ _ hn1]
    ring

/-- Separability turns any nonzero infinitesimal coordinate into the
nilpotent preimage needed for dual-number surjectivity. -/
theorem dualNumber_surjective_of_separable [Algebra.IsSeparable k L]
    (h : A →ₐ[k] DualNumber L)
    (hres : Function.Surjective (fun a => (h a).fst))
    (hdir : ∃ a, (h a).snd ≠ 0) : Function.Surjective h := by
  apply dualNumber_surjective_of_residue_and_nilpotent h hres
  obtain ⟨a, ha⟩ := hdir
  let P := minpoly k (h a).fst
  have hm : Polynomial.aeval (h a).fst P = 0 := minpoly.aeval k _
  have hd : Polynomial.aeval (h a).fst P.derivative ≠ 0 :=
    (Algebra.IsSeparable.isSeparable k (h a).fst).aeval_derivative_ne_zero hm
  refine ⟨Polynomial.aeval a P, ?_, ?_⟩
  · rw [← Polynomial.aeval_algHom_apply h]
    simpa only [polynomial_aeval_dual_fst] using hm
  · rw [← Polynomial.aeval_algHom_apply h]
    rw [polynomial_aeval_dual_snd]
    exact mul_ne_zero hd ha

end DualSurjectivity

section AffinePoint

variable {k L : Type u} [Field k] [Field L] [Algebra k L]

/-- Evaluation at the dual point with residue `p` and tangent direction `v`. -/
noncomputable def affineFirstJet (p v : Fin 3 → L) : AffineThreeRing k →ₐ[k] DualNumber L :=
  MvPolynomial.aeval
    (fun i => (TrivSqZeroExt.inl (p i) + TrivSqZeroExt.inr (v i) : DualNumber L))

theorem affineFirstJet_X_fst (p v : Fin 3 → L) (i : Fin 3) :
    (affineFirstJet p v (MvPolynomial.X (R := k) i)).fst = p i := by
  rw [affineFirstJet, MvPolynomial.aeval_X]
  simp

theorem affineFirstJet_X_snd (p v : Fin 3 → L) (i : Fin 3) :
    (affineFirstJet p v (MvPolynomial.X (R := k) i)).snd = v i := by
  rw [affineFirstJet, MvPolynomial.aeval_X]
  simp

theorem affineFirstJet_fst (p v : Fin 3 → L) (F : AffineThreeRing k) :
    (affineFirstJet p v F).fst = MvPolynomial.aeval p F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [affineFirstJet, TrivSqZeroExt.algebraMap_eq_inl']
  | add F G hF hG => simp only [map_add, fst_add, hF, hG]
  | mul_X F j hF =>
    rw [map_mul, fst_mul, hF]
    rw [affineFirstJet_X_fst]
    change MvPolynomial.aeval p F * p j = MvPolynomial.aeval p (F * X j)
    rw [map_mul, aeval_X]

theorem affineFirstJet_snd (p v : Fin 3 → L) (F : AffineThreeRing k) :
    (affineFirstJet p v F).snd = ∑ i, MvPolynomial.aeval p (pderiv i F) * v i := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [affineFirstJet, TrivSqZeroExt.algebraMap_eq_inl']
  | add F G hF hG =>
    simp only [map_add, snd_add, hF, hG, add_mul, Finset.sum_add_distrib]
  | mul_X F j hF =>
    rw [map_mul, DualNumber.snd_mul, affineFirstJet_fst, hF]
    rw [affineFirstJet_X_snd, affineFirstJet_X_fst]
    change MvPolynomial.aeval p F * v j +
        (∑ i, MvPolynomial.aeval p (pderiv i F) * v i) * p j =
      ∑ i, MvPolynomial.aeval p (pderiv i (F * X j)) * v i
    simp only [pderiv_mul, map_add, map_mul,
      pderiv_X, Pi.single_apply]
    fin_cases j <;> simp [Fin.sum_univ_three] <;> ring

/-- The directional differential at an affine point. -/
noncomputable def affineDifferential (p : Fin 3 → L) (F : AffineThreeRing k) :
    (Fin 3 → L) →ₗ[L] L where
  toFun v := ∑ i, MvPolynomial.aeval p (pderiv i F) * v i
  map_add' v w := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a v := by
    simp [Finset.mul_sum, mul_assoc, mul_left_comm]

/-- Varying the affine equation gives a `k`-linear map to its differential. -/
noncomputable def affineDifferentialMap (p : Fin 3 → L) :
    AffineThreeRing k →ₗ[k] ((Fin 3 → L) →ₗ[L] L) where
  toFun F := affineDifferential p F
  map_add' F G := by
    apply LinearMap.ext
    intro v
    change affineDifferential p (F + G) v = affineDifferential p F v + affineDifferential p G v
    simp [affineDifferential, add_mul, Finset.sum_add_distrib]
  map_smul' c F := by
    apply LinearMap.ext
    intro v
    change affineDifferential p (c • F) v = c • affineDifferential p F v
    simp [affineDifferential, Finset.mul_sum, Algebra.smul_def, mul_assoc]

/-- At a smooth affine point, the tangent space to a hypersurface in three
variables has dimension two. -/
theorem affineTangentSpace_finrank (p : Fin 3 → L) (F : AffineThreeRing k)
    (hF : affineDifferential p F ≠ 0) :
    Module.finrank L (LinearMap.ker (affineDifferential p F)) = 2 := by
  have hsurj := surjective_of_nonzero_of_finrank_eq_one (Module.finrank_self L) hF
  have h := (affineDifferential p F).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj] at h
  simp only [finrank_top] at h
  simp only [Module.finrank_self, Module.finrank_pi, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h
  omega

theorem affineFirstJet_eq_zero_iff (p v : Fin 3 → L) (F : AffineThreeRing k) :
    affineFirstJet p v F = 0 ↔
      MvPolynomial.aeval p F = 0 ∧ affineDifferential p F v = 0 := by
  constructor
  · intro h
    constructor
    · simpa [affineFirstJet_fst] using congrArg TrivSqZeroExt.fst h
    · simpa [affineFirstJet_snd, affineDifferential] using congrArg TrivSqZeroExt.snd h
  · rintro ⟨h0, h1⟩
    apply TrivSqZeroExt.ext
    · simpa [affineFirstJet_fst] using h0
    · simpa [affineFirstJet_snd, affineDifferential] using h1

theorem affineFirstJet_surjective [Algebra.IsSeparable k L] (p v : Fin 3 → L)
    (hp : Function.Surjective (MvPolynomial.aeval p : AffineThreeRing k →ₐ[k] L))
    (hv : v ≠ 0) : Function.Surjective (affineFirstJet (k := k) p v) := by
  apply dualNumber_surjective_of_separable
  · simpa only [affineFirstJet_fst] using hp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    refine ⟨X i, ?_⟩
    rwa [affineFirstJet_X_snd]

/-- The dual-point map factors through the affine hypersurface when the
point and its tangent direction annihilate its equation. -/
noncomputable def affineHypersurfaceJet (p v : Fin 3 → L) (F : AffineThreeRing k)
    (hF : affineFirstJet p v F = 0) :
    (AffineThreeRing k ⧸ Ideal.span {F}) →ₐ[k] DualNumber L :=
  Ideal.Quotient.liftₐ _ (affineFirstJet p v) (by
    change Ideal.span {F} ≤ RingHom.ker (affineFirstJet p v).toRingHom
    rw [Ideal.span_le]
    intro a ha
    rw [Set.mem_singleton_iff.mp ha]
    change affineFirstJet p v F = 0
    exact hF)

theorem affineHypersurfaceJet_surjective [Algebra.IsSeparable k L]
    (p v : Fin 3 → L) (F : AffineThreeRing k)
    (hp : Function.Surjective (MvPolynomial.aeval p : AffineThreeRing k →ₐ[k] L))
    (hv : v ≠ 0) (hF : affineFirstJet p v F = 0) :
    Function.Surjective (affineHypersurfaceJet p v F hF) := by
  intro x
  obtain ⟨a, ha⟩ := affineFirstJet_surjective p v hp hv x
  exact ⟨Ideal.Quotient.mk _ a, ha⟩

/-- A nonzero tangent vector therefore gives an actual closed immersion of
the dual-number point into the affine cubic hypersurface. -/
theorem affineHypersurfaceJet_closedImmersion [Algebra.IsSeparable k L]
    (p v : Fin 3 → L) (F : AffineThreeRing k)
    (hp : Function.Surjective (MvPolynomial.aeval p : AffineThreeRing k →ₐ[k] L))
    (hv : v ≠ 0) (hF : affineFirstJet p v F = 0) :
    IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (affineHypersurfaceJet p v F hF).toRingHom)) :=
  IsClosedImmersion.spec_of_surjective _
    (affineHypersurfaceJet_surjective p v F hp hv hF)

end AffinePoint
end QuarticNet
end PfaffianDescent
