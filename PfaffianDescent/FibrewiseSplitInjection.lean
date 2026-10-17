import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Residue-field injectivity and arbitrary base change over a local ring

For a map from a finite module into a finite free module over a local ring,
injectivity after passing to the residue field gives a linear retraction.
The retraction persists after tensoring with any coefficient algebra. This
is the degreewise algebraic bridge needed for universal regularity of a
homogeneous equation over parameter charts.
-/

namespace PfaffianDescent

open IsLocalRing

universe u v w

/-- Over a local ring, residue-field injectivity of a map into a finite
free module persists after arbitrary coefficient extension. -/
theorem lTensor_injective_of_residueField_injective
    {R : Type u} {M : Type v} {N : Type w}
    [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N] [Module.Free R N]
    (f : M →ₗ[R] N)
    (hf : Function.Injective (f.lTensor (ResidueField R)))
    (S : Type u) [CommRing S] [Algebra R S] :
    Function.Injective (f.lTensor S) := by
  obtain ⟨g, hg⟩ :=
    (IsLocalRing.split_injective_iff_lTensor_residueField_injective f).mpr hf
  have hcomp : g.lTensor S ∘ₗ f.lTensor S = LinearMap.id := by
    rw [← LinearMap.lTensor_comp, hg, LinearMap.lTensor_id]
  exact Function.HasLeftInverse.injective ⟨_, LinearMap.congr_fun hcomp⟩

/-- In particular, residue-field injectivity yields injectivity modulo
every ideal of a local coefficient ring. -/
theorem lTensor_quotient_injective_of_residueField_injective
    {R : Type u} {M : Type v} {N : Type w}
    [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N] [Module.Free R N]
    (f : M →ₗ[R] N)
    (hf : Function.Injective (f.lTensor (ResidueField R)))
    (I : Ideal R) :
    Function.Injective (f.lTensor (R ⧸ I)) :=
  lTensor_injective_of_residueField_injective f hf (R ⧸ I)

/-- The cokernel of such a map is free, hence flat, over the local base.
For a homogeneous multiplication map this is the degreewise flatness of
the corresponding equation quotient. -/
theorem cokernel_flat_of_residueField_injective
    {R : Type u} {M : Type v} {N : Type w}
    [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N] [Module.Free R N]
    (f : M →ₗ[R] N)
    (hf : Function.Injective (f.lTensor (ResidueField R))) :
    Module.Flat R (N ⧸ LinearMap.range f) := by
  haveI : Module.Free R (N ⧸ LinearMap.range f) :=
    Module.free_of_lTensor_residueField_injective f
      (LinearMap.range f).mkQ (Submodule.mkQ_surjective _)
      f.exact_map_mkQ_range hf
  infer_instance

end PfaffianDescent
