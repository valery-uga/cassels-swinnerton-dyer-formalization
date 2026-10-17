import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNativeAffineCurve

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- Flatness of the literal quotient spectrum map transports to the actual
closed affine chart using its native quotient presentation. -/
theorem cubicClosedPointSerreFiniteZeroResidual_affine_quotient_flat_transport
    {X Y Z : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (i : Z ⟶ X) (I : Ideal Γ(X, ⊤))
    (e : Z ≅ Spec (.of (Γ(X, ⊤) ⧸ I)))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) =
      i ≫ X.isoSpec.hom)
    [Flat (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ Spec.map f.appTop)] :
    Flat (i ≫ f) := by
  have hc : e.hom ≫ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫
      Spec.map f.appTop) = (i ≫ f) ≫ Y.isoSpec.hom := by
    rw [← Category.assoc, he, Category.assoc, Scheme.isoSpec_hom_naturality,
      ← Category.assoc]
  exact (MorphismProperty.arrow_mk_iso_iff @Flat
    (Arrow.isoMk e Y.isoSpec hc)).mpr inferInstance

end PfaffianDescent
