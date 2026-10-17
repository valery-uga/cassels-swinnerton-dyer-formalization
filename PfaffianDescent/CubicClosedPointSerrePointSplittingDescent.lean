import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Tower

noncomputable section
open scoped TensorProduct
namespace PfaffianDescent
universe u

/-- A field extension reflects surjectivity of the literal tensor extension.
This keeps the original field and its scalar extension separate. -/
theorem pointSplitting_surjective_of_baseChange
    {F E V W : Type u} [Field F] [Field E] [Algebra F E]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    (r : V →ₗ[F] W) (h : Function.Surjective (r.baseChange E)) :
    Function.Surjective r := by
  letI : Module.FaithfullyFlat F E := Module.FaithfullyFlat.of_flat_of_isLocalHom
  apply (Module.FaithfullyFlat.lTensor_surjective_iff_surjective F E r).mp
  simpa only [LinearMap.baseChange_eq_ltensor] using h

/-- With the actual source and finite-scheme target dimensions established,
restriction surjectivity gives the three-dimensional native kernel. -/
theorem pointSplitting_restriction_kernel_finrank_three
    {F V W : Type u} [Field F]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    [FiniteDimensional F V] (r : V →ₗ[F] W)
    (hv : Module.finrank F V = 9) (hw : Module.finrank F W = 6)
    (hr : Function.Surjective r) : Module.finrank F r.ker = 3 := by
  have h := LinearMap.finrank_range_add_finrank_ker r
  have he : r.range = ⊤ := LinearMap.range_eq_top.mpr hr
  rw [he, finrank_top, hv, hw] at h
  omega

end PfaffianDescent
