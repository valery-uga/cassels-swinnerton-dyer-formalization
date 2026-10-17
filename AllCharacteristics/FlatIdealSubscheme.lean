import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Flat ideal-defined affine subschemes

This file transfers flatness of an affine quotient algebra to the actual
ideal-defined closed subscheme.  It is used when a geometric zero locus has
been identified with a concrete quotient by a regular sequence.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry Scheme

namespace AllCharacteristics
universe u

/-- An ideal-defined subscheme of an affine scheme is the spectrum of the
quotient of its global-coordinate ring by the global ideal. -/
noncomputable def idealSubschemeIsoSpecQuotient
    {X : Scheme.{u}} [IsAffine X] (I : X.IdealSheafData) :
    I.subscheme ≅ Spec (.of
      (Γ(X, ⊤) ⧸ I.ideal ⟨⊤, isAffineOpen_top X⟩)) := by
  let : IsAffine I.subscheme := isAffine_of_isAffineHom I.subschemeι
  let U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  let e := I.subschemeObjIso U
  change Γ(I.subscheme, ⊤) ≅ .of
    (Γ(X, ⊤) ⧸ I.ideal ⟨⊤, isAffineOpen_top X⟩) at e
  exact I.subscheme.isoSpec ≪≫ Scheme.Spec.mapIso e.symm.op

/-- The affine quotient presentation commutes with the closed immersion into
the ambient affine scheme. -/
theorem idealSubschemeIsoSpecQuotient_hom_comp
    {X : Scheme.{u}} [IsAffine X] (I : X.IdealSheafData) :
    (idealSubschemeIsoSpecQuotient I).hom ≫
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I.ideal ⟨⊤, isAffineOpen_top X⟩))) =
      I.subschemeι ≫ X.isoSpec.hom := by
  let : IsAffine I.subscheme := isAffine_of_isAffineHom I.subschemeι
  let U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  let e := I.subschemeObjIso U
  change Γ(I.subscheme, ⊤) ≅ .of
    (Γ(X, ⊤) ⧸ I.ideal ⟨⊤, isAffineOpen_top X⟩) at e
  have hApp : I.subschemeι.appTop =
      CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal ⟨⊤, isAffineOpen_top X⟩)) ≫ e.inv := by
    change I.subschemeι.app U = _
    rw [I.subschemeι_app U]
    rfl
  rw [← Scheme.isoSpec_hom_naturality]
  change (I.subscheme.isoSpec ≪≫ Scheme.Spec.mapIso e.symm.op).hom ≫
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I.ideal ⟨⊤, isAffineOpen_top X⟩))) = _
  dsimp only [Iso.trans_hom]
  rw [Category.assoc, Scheme.Spec.mapIso_hom, hApp]
  rw [Spec.map_comp]
  rfl

/-- The affine quotient presentation of an ideal-defined subscheme is also
compatible with every morphism from the ambient affine scheme to an affine
base. -/
theorem idealSubschemeIsoSpecQuotient_hom_comp_to_isoSpec
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (g : X ⟶ Y) (I : X.IdealSheafData) :
    (idealSubschemeIsoSpecQuotient I).hom ≫
      Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk (I.ideal ⟨⊤, isAffineOpen_top X⟩)).comp g.appTop.hom)) =
      I.subschemeι ≫ g ≫ Y.isoSpec.hom := by
  rw [show CommRingCat.ofHom
      ((Ideal.Quotient.mk (I.ideal ⟨⊤, isAffineOpen_top X⟩)).comp g.appTop.hom) =
      g.appTop ≫ CommRingCat.ofHom
        (Ideal.Quotient.mk (I.ideal ⟨⊤, isAffineOpen_top X⟩)) by rfl]
  rw [Spec.map_comp, ← Category.assoc,
    idealSubschemeIsoSpecQuotient_hom_comp I]
  rw [Category.assoc, Scheme.isoSpec_hom_naturality]

/-- If the quotient of the global-coordinate ring of an affine scheme is
flat over a base coordinate ring, then the ideal-defined subscheme is flat
over the base on global coordinates. -/
theorem flat_subscheme_comp_appTop_of_flat_quotient
    {X Y : Scheme.{u}} [IsAffine X]
    (f : X ⟶ Y) (I : Scheme.IdealSheafData X)
    (hflat :
      ((Ideal.Quotient.mk (I.ideal ⟨⊤, isAffineOpen_top X⟩)).comp f.appTop.hom).Flat) :
    ((I.subschemeι ≫ f).appTop.hom).Flat := by
  rw [Scheme.Hom.comp_appTop]
  change RingHom.Flat (CommRingCat.Hom.hom (f.appTop ≫ I.subschemeι.app ⊤))
  rw [I.subschemeι_app ⟨⊤, isAffineOpen_top X⟩]
  rw [← Category.assoc]
  have hq : (f.appTop ≫ CommRingCat.ofHom
      (Ideal.Quotient.mk (I.ideal ⟨⊤, isAffineOpen_top X⟩))).hom.Flat := by
    exact hflat
  apply RingHom.Flat.comp hq
  apply RingHom.Flat.of_bijective
  exact ConcreteCategory.bijective_of_isIso
    (I.subschemeObjIso ⟨⊤, isAffineOpen_top X⟩).inv

/-- Flatness of a quotient map is unchanged after replacing its defining
ideal by an equal ideal. -/
theorem flat_quotient_comp_of_ideal_eq
    {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A) (I J : Ideal A) (hIJ : I = J)
    (hflat : ((Ideal.Quotient.mk J).comp φ).Flat) :
    ((Ideal.Quotient.mk I).comp φ).Flat := by
  let e : (A ⧸ I) ≃+* (A ⧸ J) := Ideal.quotEquivOfEq hIJ
  have he : e.symm.toRingHom.Flat :=
    RingHom.Flat.of_bijective e.symm.bijective
  have h := RingHom.Flat.comp hflat he
  have hcomp : e.symm.toRingHom.comp ((Ideal.Quotient.mk J).comp φ) =
      (Ideal.Quotient.mk I).comp φ := by
    ext r
    change e.symm (Ideal.Quotient.mk J (φ r)) = Ideal.Quotient.mk I (φ r)
    rw [← Ideal.quotEquivOfEq_mk hIJ]
    exact e.symm_apply_apply _
  rw [hcomp] at h
  exact h

/-- If the quotient of the global-coordinate ring of an affine scheme is
flat over an affine base, then the corresponding ideal-defined subscheme is
flat over that base. -/
theorem flat_subscheme_comp_of_flat_quotient
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (I : Scheme.IdealSheafData X)
    (hflat :
      ((Ideal.Quotient.mk (I.ideal ⟨⊤, isAffineOpen_top X⟩)).comp f.appTop.hom).Flat) :
    Flat (I.subschemeι ≫ f) := by
  let _ : IsAffine I.subscheme := isAffine_of_isAffineHom I.subschemeι
  rw [HasRingHomProperty.iff_of_isAffine (P := @Flat)]
  exact flat_subscheme_comp_appTop_of_flat_quotient f I hflat

/-- A concrete quotient presentation of the global ideal gives flatness of
the corresponding ideal-defined subscheme over an affine base. -/
theorem flat_subscheme_comp_of_flat_quotient_eq
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (I : Scheme.IdealSheafData X) (J : Ideal Γ(X, ⊤))
    (hIJ : I.ideal ⟨⊤, isAffineOpen_top X⟩ = J)
    (hflat : ((Ideal.Quotient.mk J).comp f.appTop.hom).Flat) :
    Flat (I.subschemeι ≫ f) := by
  apply flat_subscheme_comp_of_flat_quotient f I
  exact flat_quotient_comp_of_ideal_eq f.appTop.hom
    (I.ideal ⟨⊤, isAffineOpen_top X⟩) J hIJ hflat

end AllCharacteristics
