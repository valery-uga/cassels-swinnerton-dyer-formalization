import PfaffianDescent.WholeIdealEmbeddedScalarCartesian296

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- A derived ordinary whole-ideal image equality yields the exact native embedding-kernel
pullback equality. Both nilpotents and the canonical coefficient map are retained. -/
lemma nativePolynomialIdealImageKernel_comap300
    {C S : Type u} [CommRing C] [CommRing S] {m : ℕ}
    (f : C →+* S) (I : Ideal (MvPolynomial (Fin m) C))
    (J : Ideal (MvPolynomial (Fin m) S))
    (h : I.map (MvPolynomial.map f) = J) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap
      (Spec.map (CommRingCat.ofHom (MvPolynomial.map f))) =
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).ker := by
  letI : Algebra C S := f.toAlgebra
  have hc := wholeIdealEmbeddedScalar_kernel_comap296 (C := C) (S := S) I
  exact hc.trans (congrArg
    (fun K : Ideal (MvPolynomial (Fin m) S) =>
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))).ker) h)

/-- An internally derived exact ideal pullback equality gives the native closed-family
comparison Iso, using IdealSheafData.comapIso rather than a supplied Iso premise. -/
def nativeClosedIdealComparisonIso300
    {X Y : Scheme.{u}} (I : Y.IdealSheafData) (a : X ⟶ Y)
    (J : X.IdealSheafData) (h : I.comap a = J) :
    J.subscheme ≅ pullback a I.subschemeι :=
  (eqToIso (congrArg (fun K : X.IdealSheafData => K.subscheme) h.symm)) ≪≫ I.comapIso a

lemma nativeClosedIdealComparisonIso_hom_fst300
    {X Y : Scheme.{u}} (I : Y.IdealSheafData) (a : X ⟶ Y)
    (J : X.IdealSheafData) (h : I.comap a = J) :
    (nativeClosedIdealComparisonIso300 I a J h).hom ≫ pullback.fst a I.subschemeι =
      J.subschemeι := by
  subst J
  simpa only [nativeClosedIdealComparisonIso300, eqToIso_refl, Iso.refl_trans] using I.comapIso_hom_fst a

end PfaffianDescent
