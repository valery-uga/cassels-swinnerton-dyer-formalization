import Mathlib.RingTheory.Flat.Tensor

/-!
# A flatness criterion for a presented quotient

For an exact presentation of a quotient of a flat module, injectivity of the
relation map after tensoring with every quotient of the base ring implies
flatness of the presented module. The proof is an explicit tensor diagram
chase, with no finiteness, noetherian, or characteristic assumptions.
-/

open LinearMap TensorProduct
namespace AllCharacteristics
universe u v w t

/-- A quotient of a flat module is flat if the relation map remains injective
after tensoring with every quotient of the coefficient ring. -/
theorem flat_of_exact_of_quotient_tensor_injective
    {R : Type u} [CommRing R]
    {M : Type v} {N : Type w} {P : Type t}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] [Module.Flat R N]
    (g : M →ₗ[R] N) (f : N →ₗ[R] P) (hf : Function.Surjective f)
    (hex : Function.Exact g f)
    (hinj : ∀ I : Ideal R, Function.Injective (g.lTensor (R ⧸ I))) :
    Module.Flat R P := by
  apply Module.Flat.iff_rTensor_injective'.mpr
  intro I
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨y, rfl⟩ := lTensor_surjective I hf x
  have hy : (f.lTensor R) ((I.subtype.rTensor N) y) = 0 := by
    rw [← LinearMap.comp_apply, lTensor_comp_rTensor,
      ← rTensor_comp_lTensor, LinearMap.comp_apply]
    exact hx
  obtain ⟨m, hm⟩ := (lTensor_exact R hex hf _).mp hy
  have hm0 : (I.mkQ.rTensor M) m = 0 := by
    apply hinj I
    rw [map_zero, ← LinearMap.comp_apply, lTensor_comp_rTensor,
      ← rTensor_comp_lTensor, LinearMap.comp_apply, hm,
      ← LinearMap.comp_apply, ← rTensor_comp]
    rw [(LinearMap.exact_subtype_mkQ I).linearMap_comp_eq_zero, rTensor_zero,
      LinearMap.zero_apply]
  obtain ⟨z, hz⟩ := (rTensor_exact M (LinearMap.exact_subtype_mkQ I)
    I.mkQ_surjective m).mp hm0
  have hyz : y = (g.lTensor I) z := by
    apply Module.Flat.rTensor_preserves_injective_linearMap I.subtype I.subtype_injective
    rw [← hm, ← hz, ← LinearMap.comp_apply, lTensor_comp_rTensor,
      ← rTensor_comp_lTensor, LinearMap.comp_apply]
  rw [hyz]
  exact congrArg (fun h : I ⊗[R] M →ₗ[R] I ⊗[R] P ↦ h z)
    (lTensor_exact I hex hf).linearMap_comp_eq_zero

end AllCharacteristics
