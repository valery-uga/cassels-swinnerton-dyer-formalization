import Mathlib.RingTheory.Flat.Tensor
import Mathlib.RingTheory.TensorProduct.Quotient

/-! The tensor injection for the actual quotient, derived from ambient
flatness and the explicit ideal intersection calculation. -/

open LinearMap TensorProduct
namespace AllCharacteristics
universe u v w

def idealTensorMultiplication166
    {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] :
    I ⊗[R] M →ₗ[R] M :=
  (TensorProduct.lid R M).toLinearMap.comp (I.subtype.rTensor M)

theorem idealTensorMultiplication166_range
    {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] :
    (idealTensorMultiplication166 I M).range = I • (⊤ : Submodule R M) :=
  I.subtype_rTensor_range M

theorem idealTensorMultiplication166_naturality
    {R : Type u} [CommRing R] (I : Ideal R)
    {M : Type v} {N : Type w} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) :
    (idealTensorMultiplication166 I N).comp (f.lTensor I) =
      f.comp (idealTensorMultiplication166 I M) := by
  ext r m
  simp [idealTensorMultiplication166]

theorem idealTensorMultiplication166_injective_of_flat
    {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Flat R M] :
    Function.Injective (idealTensorMultiplication166 I M) :=
  (TensorProduct.lid R M).injective.comp
    (Module.Flat.rTensor_preserves_injective_linearMap I.subtype I.subtype_injective)

/-- The desired tensor injection is proved by a quotient diagram chase; it
is not supplied as a hypothesis.  The explicit intersection hypothesis is
discharged by the lifted-regular-pair producer in the actual ring caller. -/
theorem idealTensorMultiplication166_injective_of_ker_intersection
    {R : Type u} [CommRing R] (I : Ideal R)
    {M : Type v} {N : Type w} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module.Flat R M]
    (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (hinter : f.ker ⊓ I • (⊤ : Submodule R M) = I • f.ker) :
    Function.Injective (idealTensorMultiplication166 I N) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨y, rfl⟩ := f.lTensor_surjective I hf x
  have hyker : idealTensorMultiplication166 I M y ∈ f.ker := by
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply,
      ← idealTensorMultiplication166_naturality I f, LinearMap.comp_apply]
    exact hx
  have hyI : idealTensorMultiplication166 I M y ∈ I • (⊤ : Submodule R M) := by
    rw [← idealTensorMultiplication166_range I M]
    exact LinearMap.mem_range_self _ y
  have hys : idealTensorMultiplication166 I M y ∈ I • f.ker := by
    rw [← hinter]
    exact ⟨hyker, hyI⟩
  have hys' : (⟨idealTensorMultiplication166 I M y, hyker⟩ : f.ker) ∈
      I • (⊤ : Submodule R f.ker) :=
    (Submodule.mem_smul_top_iff I f.ker _).mpr hys
  rw [← idealTensorMultiplication166_range I f.ker] at hys'
  obtain ⟨z, hz⟩ := hys'
  have hzy : f.ker.subtype.lTensor I z = y := by
    apply idealTensorMultiplication166_injective_of_flat I M
    calc
      idealTensorMultiplication166 I M (f.ker.subtype.lTensor I z) =
          f.ker.subtype (idealTensorMultiplication166 I f.ker z) :=
        congrArg (fun h : I ⊗[R] f.ker →ₗ[R] M => h z)
          (idealTensorMultiplication166_naturality I f.ker.subtype)
      _ = idealTensorMultiplication166 I M y := by rw [hz]; rfl
  rw [← hzy, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
    (LinearMap.exact_subtype_ker_map f).linearMap_comp_eq_zero,
    LinearMap.lTensor_zero, LinearMap.zero_apply]

/-- Actual quotient by an entire ideal.  Ambient flatness plus the explicit
whole-ideal intersection implies the canonical base-ideal tensor injection. -/
theorem quotient_idealTensorMultiplication166_injective
    {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    [Algebra R A] [Module.Flat R A] (I : Ideal R) (J : Ideal A)
    (hinter : I.map (algebraMap R A) ⊓ J = I.map (algebraMap R A) * J) :
    Function.Injective (idealTensorMultiplication166 I (A ⧸ J)) := by
  let f := (Ideal.Quotient.mkₐ R J).toLinearMap
  have hker : f.ker = J.restrictScalars R := by
    ext x
    change Ideal.Quotient.mk J x = 0 ↔ x ∈ J
    exact Ideal.Quotient.eq_zero_iff_mem
  have hright : I • f.ker =
      (I.map (algebraMap R A) * J).restrictScalars R := by
    rw [hker, ← Ideal.smul_restrictScalars I J, Ideal.smul_eq_mul]
  apply idealTensorMultiplication166_injective_of_ker_intersection I f
    Ideal.Quotient.mk_surjective
  calc
    f.ker ⊓ I • (⊤ : Submodule R A) =
        (J ⊓ I.map (algebraMap R A)).restrictScalars R := by
      rw [hker, Ideal.smul_top_eq_map]
      rfl
    _ = (I.map (algebraMap R A) * J).restrictScalars R := by
      rw [inf_comm, hinter]
    _ = I • f.ker := hright.symm

end AllCharacteristics
