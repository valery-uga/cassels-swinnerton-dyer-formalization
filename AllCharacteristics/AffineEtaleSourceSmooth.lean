import AllCharacteristics.EtaleSourceHomology
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # Smoothness descent for actual affine scheme maps -/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u

/-- A locally finitely presented map of affine schemes is smooth when its
composite with a surjective étale affine cover is smooth. -/
lemma smooth_of_surjective_etale_between_affines
    {X Y Z : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine Z]
    (q : X ⟶ Y) [Etale q] [Surjective q]
    (p : Y ⟶ Z) [LocallyOfFinitePresentation p] [Smooth (q ≫ p)] : Smooth p := by
  let := p.appTop.hom.toAlgebra
  let := q.appTop.hom.toAlgebra
  let := (q ≫ p).appTop.hom.toAlgebra
  have : IsScalarTower Γ(Z, ⊤) Γ(Y, ⊤) Γ(X, ⊤) :=
    IsScalarTower.of_algebraMap_eq' (by
      change (q ≫ p).appTop.hom = q.appTop.hom.comp p.appTop.hom
      rw [Scheme.Hom.comp_appTop]
      rfl)
  have : Algebra.Etale Γ(Y, ⊤) Γ(X, ⊤) :=
    RingHom.etale_algebraMap.mp (show (algebraMap Γ(Y, ⊤) Γ(X, ⊤)).Etale from
      (HasRingHomProperty.iff_of_isAffine (P := @Etale.{u})).mp inferInstance)
  have : Algebra.FinitePresentation Γ(Z, ⊤) Γ(Y, ⊤) :=
    RingHom.finitePresentation_algebraMap.mp
      (show (algebraMap Γ(Z, ⊤) Γ(Y, ⊤)).FinitePresentation from
        (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation.{u})).mp inferInstance)
  have : Algebra.Smooth Γ(Z, ⊤) Γ(X, ⊤) :=
    RingHom.smooth_algebraMap.mp (show (algebraMap Γ(Z, ⊤) Γ(X, ⊤)).Smooth from
      (HasRingHomProperty.iff_of_isAffine (P := @Smooth.{u})).mp inferInstance)
  have : Surjective (X.isoSpec.hom ≫ Spec.map q.appTop) := by
    rw [Scheme.isoSpec_hom_naturality]
    infer_instance
  have : Surjective (Spec.map q.appTop) := Surjective.of_comp X.isoSpec.hom _
  have : Module.FaithfullyFlat Γ(Y, ⊤) Γ(X, ⊤) :=
    Module.FaithfullyFlat.of_comap_surjective (Spec.map q.appTop).surjective
  apply (HasRingHomProperty.iff_of_isAffine (P := @Smooth.{u})).mpr
  exact RingHom.smooth_algebraMap.mpr
    (smooth_of_faithfullyFlat_etale Γ(Z, ⊤) Γ(Y, ⊤) Γ(X, ⊤))

end AllCharacteristics
