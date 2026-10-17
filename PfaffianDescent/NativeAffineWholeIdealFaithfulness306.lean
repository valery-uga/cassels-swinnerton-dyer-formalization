import PfaffianDescent.NativeWholeIdealChartFamily302
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

/-- Recover the entire ring-theoretic kernel from the native Spec kernel at top.
The comparison uses the actual Gamma-Spec isomorphism, and retains nilpotents. -/
lemma nativeSpecMap_kernel_top306
    {C D : Type u} [CommRing C] [CommRing D] (f : C →+* D) :
    (Spec.map (CommRingCat.ofHom f)).ker.ideal
        ⟨⊤, isAffineOpen_top (Spec (.of C))⟩ =
      (RingHom.ker f).comap (Scheme.ΓSpecIso (.of C)).hom.hom := by
  rw [Scheme.Hom.ker_apply]
  change RingHom.ker (Spec.map (CommRingCat.ofHom f)).appTop.hom = _
  rw [← RingHom.ker_equiv_comp _
    (Scheme.ΓSpecIso (.of D)).commRingCatIsoToRingEquiv,
    RingEquiv.toRingHom_eq_coe, Iso.commRingCatIsoToRingEquiv_toRingHom,
    ← CommRingCat.hom_comp, Scheme.ΓSpecIso_naturality,
    CommRingCat.hom_comp, RingHom.comap_ker]
  rfl

/-- Equality of the native whole closed-immersion kernels forces equality of
the original whole affine ideals; no classification outcome is assumed. -/
lemma nativeAffineQuotientKernel_injective306
    {C : Type u} [CommRing C] (I J : Ideal C)
    (h : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).ker) : I = J := by
  have ht := congrArg
    (fun K : (Spec (.of C)).IdealSheafData =>
      K.ideal ⟨⊤, isAffineOpen_top (Spec (.of C))⟩) h
  rw [nativeSpecMap_kernel_top306, nativeSpecMap_kernel_top306,
    Ideal.mk_ker, Ideal.mk_ker] at ht
  exact Ideal.comap_injective_of_surjective (Scheme.ΓSpecIso (.of C)).hom.hom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of C)).hom).surjective ht

/-- The native family of a whole-ideal chart determines its exact polynomial
ideal even when the two monomial bases differ. -/
lemma monomialWholeIdealNativeFamily_sameIdeal306
    {A : Type u} [CommRing A] {m n : ℕ}
    (B C : Fin n → (Fin m →₀ ℕ))
    (x : MonomialWholeIdealChart287 (A := A) B)
    (y : MonomialWholeIdealChart287 (A := A) C)
    (h : (monomialWholeIdealNativeFamily302 B x).val =
      (monomialWholeIdealNativeFamily302 C y).val) : x.val = y.val :=
  nativeAffineQuotientKernel_injective306 x.val y.val h

end PfaffianDescent
end
