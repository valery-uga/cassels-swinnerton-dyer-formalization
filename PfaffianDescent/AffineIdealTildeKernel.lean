import PfaffianDescent.FlatAffineRegularPrincipalCartier
import PfaffianDescent.AffineQCAcyclicity

/-! On an affine scheme, tilde of a quotient ideal is the sheaf kernel. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- The ring-theoretic ideal of an affine quotient is the kernel of its
underlying linear quotient map. -/
theorem affineQuotientLinearMap_ker
    {A : Type u} [CommRing A] (I : Ideal A) :
    (Algebra.linearMap A (A ⧸ I)).ker = I := by
  ext a
  change (Ideal.Quotient.mk I) a = 0 ↔ a ∈ I
  exact Ideal.Quotient.eq_zero_iff_mem

/-- The `tilde` sheaf of an affine quotient ideal is the categorical
kernel of the corresponding morphism of `tilde` module sheaves. -/
noncomputable def affineIdealTildeKernelIso
    {A : Type u} [CommRing A] (I : Ideal A) :
    (tilde.functor (CommRingCat.of A)).obj (ModuleCat.of A I) ≅
      kernel ((tilde.functor (CommRingCat.of A)).map
        (ModuleCat.ofHom (Algebra.linearMap A (A ⧸ I)))) := by
  let f := ModuleCat.ofHom (Algebra.linearMap A (A ⧸ I))
  have hker : f.hom.ker = I := affineQuotientLinearMap_ker I
  let e : ModuleCat.of A I ≅ kernel f :=
    (LinearEquiv.ofEq I f.hom.ker hker.symm).toModuleIso ≪≫
      (ModuleCat.kernelIsoKer f).symm
  letI : (tilde.functor (CommRingCat.of A)).IsLeftAdjoint :=
    tilde.adjunction.isLeftAdjoint
  letI : (tilde.functor (CommRingCat.of A)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  letI : PreservesFiniteLimits (tilde.functor (CommRingCat.of A)) :=
    tilde_preservesFiniteLimits
  exact (tilde.functor (CommRingCat.of A)).mapIso e ≪≫
    PreservesKernel.iso (tilde.functor (CommRingCat.of A)) f

/-- The affine kernel comparison respects inclusion into the structure sheaf. -/
theorem affineIdealTildeKernelIso_hom_ι
    {A : Type u} [CommRing A] (I : Ideal A) :
    (affineIdealTildeKernelIso I).hom ≫
        kernel.ι ((tilde.functor (CommRingCat.of A)).map
          (ModuleCat.ofHom (Algebra.linearMap A (A ⧸ I)))) =
      (tilde.functor (CommRingCat.of A)).map
        (ModuleCat.ofHom I.subtype) := by
  let F := tilde.functor (CommRingCat.of A)
  let f := ModuleCat.ofHom (Algebra.linearMap A (A ⧸ I))
  have hker : f.hom.ker = I := affineQuotientLinearMap_ker I
  let e : ModuleCat.of A I ≅ kernel f :=
    (LinearEquiv.ofEq I f.hom.ker hker.symm).toModuleIso ≪≫
      (ModuleCat.kernelIsoKer f).symm
  have he : e.hom ≫ kernel.ι f = ModuleCat.ofHom I.subtype := by
    dsimp [e]
    rw [Category.assoc, ModuleCat.kernelIsoKer_inv_kernel_ι]
    apply ModuleCat.hom_ext
    ext x
    rfl
  letI : F.IsLeftAdjoint := tilde.adjunction.isLeftAdjoint
  letI : F.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  letI : PreservesFiniteLimits F := tilde_preservesFiniteLimits
  change (F.mapIso e ≪≫ PreservesKernel.iso F f).hom ≫ kernel.ι (F.map f) =
    F.map (ModuleCat.ofHom I.subtype)
  rw [Iso.trans_hom, Category.assoc, PreservesKernel.iso_hom,
    kernelComparison_comp_ι]
  change F.map e.hom ≫ F.map (kernel.ι f) = F.map (ModuleCat.ofHom I.subtype)
  rw [← F.map_comp, he]

end PfaffianDescent
