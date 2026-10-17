import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

private lemma nativeClosedIsoInverseFactor312
    {C : Type*} [Category C] {Z W Y : C} (e : Z ≅ W)
    (q : Z ⟶ Y) (i : W ⟶ Y) (h : e.hom ≫ i = q) : e.inv ≫ q = i :=
  (congrArg (fun z => e.inv ≫ z) h.symm).trans
    ((Category.assoc e.inv e.hom i).symm.trans
      ((congrArg (fun z => z ≫ i) e.inv_hom_id).trans (Category.id_comp i)))

/-- A genuine closed presentation of the whole kernel gives a native Scheme Iso. -/
def nativeClosedKernelPresentationIso312
    {Z Y : Scheme.{u}} (q : Z ⟶ Y) [IsClosedImmersion q]
    (I : Y.IdealSheafData) (h : I = q.ker) : I.subscheme ≅ Z :=
  eqToIso (congrArg (fun J : Y.IdealSheafData => J.subscheme) h) ≪≫ (asIso q.toImage).symm

lemma nativeClosedKernelPresentationIso_hom_comp312
    {Z Y : Scheme.{u}} (q : Z ⟶ Y) [IsClosedImmersion q]
    (I : Y.IdealSheafData) (h : I = q.ker) :
    (nativeClosedKernelPresentationIso312 q I h).hom ≫ q = I.subschemeι := by
  subst I
  change (asIso q.toImage).inv ≫ q = q.ker.subschemeι
  exact nativeClosedIsoInverseFactor312 (asIso q.toImage) q q.ker.subschemeι q.toImage_imageι

lemma nativeClosedKernelPresentationIso_inv_comp312
    {Z Y : Scheme.{u}} (q : Z ⟶ Y) [IsClosedImmersion q]
    (I : Y.IdealSheafData) (h : I = q.ker) :
    (nativeClosedKernelPresentationIso312 q I h).inv ≫ I.subschemeι = q :=
  nativeClosedIsoInverseFactor312 (nativeClosedKernelPresentationIso312 q I h)
    I.subschemeι q (nativeClosedKernelPresentationIso_hom_comp312 q I h)

end PfaffianDescent
end
