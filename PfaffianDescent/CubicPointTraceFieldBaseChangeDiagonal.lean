import PfaffianDescent.VoisinGaloisBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-! # The actual diagonal component of a separable point fibre

The projector is constructed from the kernel of the actual tensor
multiplication map. Its normalization and scalar identities are proved from
separability; no trace or base-change compatibility is assumed.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace PfaffianDescent
universe u

section Diagonal
variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

private theorem cubicPointTraceFieldBaseChange_kernelGenerator_exists :
    ∃ f : L ⊗[K] L, IsIdempotentElem f ∧
      KaehlerDifferential.ideal K L = Ideal.span {f} := by
  let : Algebra.FormallyUnramified K L :=
    Algebra.FormallyUnramified.of_isSeparable K L
  exact (Ideal.isIdempotentElem_iff_of_fg _
    (KaehlerDifferential.ideal_fg K L)).mp
      ((Ideal.cotangent_subsingleton_iff _).mp
        (inferInstanceAs (Subsingleton Ω[L⁄K])))

/-- The element selecting the actual diagonal rational component. -/
def cubicPointTraceFieldBaseChangeDiagonalProjector : L ⊗[K] L :=
  1 - (cubicPointTraceFieldBaseChange_kernelGenerator_exists K L).choose

theorem cubicPointTraceFieldBaseChangeDiagonalProjector_idempotent :
    IsIdempotentElem (cubicPointTraceFieldBaseChangeDiagonalProjector K L) :=
  (cubicPointTraceFieldBaseChange_kernelGenerator_exists K L).choose_spec.1.one_sub

theorem cubicPointTraceFieldBaseChangeDiagonalProjector_eval :
    Algebra.TensorProduct.lmul' K
      (cubicPointTraceFieldBaseChangeDiagonalProjector K L) = (1 : L) := by
  let f := (cubicPointTraceFieldBaseChange_kernelGenerator_exists K L).choose
  have hf : f ∈ KaehlerDifferential.ideal K L := by
    rw [(cubicPointTraceFieldBaseChange_kernelGenerator_exists K L).choose_spec.2]
    exact Ideal.mem_span_singleton_self f
  have hzero : Algebra.TensorProduct.lmul' K f = (0 : L) := hf
  change Algebra.TensorProduct.lmul' K (1 - f) = 1
  rw [map_sub, map_one, hzero, sub_zero]

theorem cubicPointTraceFieldBaseChangeDiagonalProjector_ne_zero :
    cubicPointTraceFieldBaseChangeDiagonalProjector K L ≠ 0 := by
  intro h
  have := cubicPointTraceFieldBaseChangeDiagonalProjector_eval K L
  rw [h, map_zero] at this
  exact zero_ne_one this

theorem cubicPointTraceFieldBaseChangeDiagonalProjector_annihilates_kernel
    (t : L ⊗[K] L) (ht : Algebra.TensorProduct.lmul' K t = (0 : L)) :
    t * cubicPointTraceFieldBaseChangeDiagonalProjector K L = 0 := by
  let f := (cubicPointTraceFieldBaseChange_kernelGenerator_exists K L).choose
  have hf : f * f = f :=
    (cubicPointTraceFieldBaseChange_kernelGenerator_exists K L).choose_spec.1
  have ht' : t ∈ Ideal.span {f} := by
    rw [← (cubicPointTraceFieldBaseChange_kernelGenerator_exists K L).choose_spec.2]
    exact ht
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp ht'
  change t * (1 - f) = 0
  rw [← ha, mul_assoc, mul_sub, mul_one, hf, sub_self, mul_zero]

/-- Every tensor acts on the diagonal component through actual multiplication
evaluation. -/
theorem cubicPointTraceFieldBaseChangeDiagonalProjector_mul
    (t : L ⊗[K] L) :
    t * cubicPointTraceFieldBaseChangeDiagonalProjector K L =
      Algebra.TensorProduct.lmul' K t •
        cubicPointTraceFieldBaseChangeDiagonalProjector K L := by
  have h := cubicPointTraceFieldBaseChangeDiagonalProjector_annihilates_kernel K L
    (t - Algebra.TensorProduct.lmul' K t ⊗ₜ[K] (1 : L)) (by simp)
  rw [sub_mul, sub_eq_zero] at h
  exact h.trans (by rw [Algebra.smul_def]; rfl)

/-- Right multiplication by the original point scalar agrees with scalar
extension on the selected rational component. -/
theorem cubicPointTraceFieldBaseChangeDiagonalProjector_right_scalar (a : L) :
    ((1 : L) ⊗ₜ[K] a) * cubicPointTraceFieldBaseChangeDiagonalProjector K L =
      a • cubicPointTraceFieldBaseChangeDiagonalProjector K L := by
  simpa using cubicPointTraceFieldBaseChangeDiagonalProjector_mul K L (1 ⊗ₜ[K] a)

/-- The diagonal projector is a finite linear combination of multiplication
by scalars from the original residue field. -/
theorem cubicPointTraceFieldBaseChangeDiagonalProjector_finite_scalar_combination :
    ∃ s : Finset (L × L), ∀ t : L ⊗[K] L,
      cubicPointTraceFieldBaseChangeDiagonalProjector K L * t =
        ∑ ab ∈ s, ab.1 • (((1 : L) ⊗ₜ[K] ab.2) * t) := by
  obtain ⟨s, hs⟩ := TensorProduct.exists_finset
    (cubicPointTraceFieldBaseChangeDiagonalProjector K L)
  refine ⟨s, fun t => ?_⟩
  rw [hs, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ab hab
  rw [Algebra.smul_def, ← mul_assoc]
  congr 1
  change ab.1 ⊗ₜ[K] ab.2 = (ab.1 ⊗ₜ[K] (1 : L)) * ((1 : L) ⊗ₜ[K] ab.2)
  simp

end Diagonal
end PfaffianDescent
