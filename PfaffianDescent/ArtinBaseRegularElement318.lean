import PfaffianDescent.ArtinBaseTensorInjection318
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.Algebra.Regular.SMul

/-!
A regular element on the residue fiber of a base-flat
algebra lifts to an actual regular element and a base-flat principal
quotient. Quotient flatness is proved from universal tensor injectivity.
-/

noncomputable section
namespace AllCharacteristics
open Module LinearMap TensorProduct
universe u v

theorem regularElement_and_flat_quotient_of_nilpotent_residue318
    {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    [Algebra R A] [Module.Flat R A]
    (I : Ideal R) [I.IsMaximal] (hI : IsNilpotent I) (a : A)
    (hreg : IsSMulRegular ((R ⧸ I) ⊗[R] A) ((1 : R ⧸ I) ⊗ₜ[R] a)) :
    IsSMulRegular A a ∧ Module.Flat R (A ⧸ Ideal.span {a}) := by
  let k := R ⧸ I
  let g := LinearMap.mulLeft R a
  have hg : g.lTensor k =
      LinearMap.mulLeft R ((1 : k) ⊗ₜ[R] a : k ⊗[R] A) := by
    ext r x
    simp [g, Algebra.TensorProduct.tmul_mul_tmul]
  have hred : Function.Injective (g.lTensor k) := by
    rw [hg]
    exact hreg
  have hactual : Function.Injective g :=
    injective_of_nilpotent_residue_of_flat318 I hI g hred
  refine ⟨hactual, ?_⟩
  let f := (Ideal.Quotient.mkₐ R (Ideal.span {a})).toLinearMap
  apply flat_of_exact_of_quotient_tensor_injective g f Ideal.Quotient.mk_surjective
  · intro x
    change Ideal.Quotient.mk (Ideal.span {a}) x = 0 ↔ ∃ y, a * y = x
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, dvd_def]
    exact exists_congr fun _ => eq_comm
  · intro J
    exact lTensor_injective_of_nilpotent_residue318 I hI g hred (R ⧸ J)

end AllCharacteristics
end
