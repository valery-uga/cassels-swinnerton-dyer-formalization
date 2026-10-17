import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # Finite spectrum coproducts with a small indexing type -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u

/-- The finite constant spectrum coproduct comparison is an isomorphism even
when its finite indexing type and coefficient ring have different universes. -/
theorem isIso_sigmaSpec_const_finite (G : Type) [Finite G] (B : Type u) [CommRing B] :
    IsIso (sigmaSpec (fun _ : G ↦ CommRingCat.of B)) := by
  let ε : ULift.{u} G ≃ G := Equiv.ulift
  let e := RingEquiv.piCongrLeft (fun _ : G ↦ B) ε
  let τ : CommRingCat.of (G → B) ⟶ CommRingCat.of (ULift.{u} G → B) :=
    CommRingCat.ofHom e.symm.toRingHom
  let j := (Sigma.reindex ε (fun _ : G ↦ Spec (.of B))).hom
  have hj : IsIso j := inferInstance
  have hτ : IsIso (Spec.map τ) := isIso_SpecMap_iff.mpr e.symm.bijective
  have hs : IsIso (sigmaSpec (fun _ : ULift.{u} G ↦ CommRingCat.of B)) := inferInstance
  have he : j ≫ sigmaSpec (fun _ : G ↦ CommRingCat.of B) =
      sigmaSpec (fun _ : ULift.{u} G ↦ CommRingCat.of B) ≫ Spec.map τ := by
    apply Sigma.hom_ext
    intro g
    have hι : Sigma.ι ((fun _ : G ↦ Spec (.of B)) ∘ ε) g ≫
        sigmaSpec (fun _ : ULift.{u} G ↦ CommRingCat.of B) =
          Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : ULift.{u} G ↦ B) g)) :=
      ι_sigmaSpec (fun _ : ULift.{u} G ↦ CommRingCat.of B) g
    rw [← Category.assoc, Sigma.ι_reindex_hom, ι_sigmaSpec,
      ← Category.assoc, hι, ← Spec.map_comp]
    rfl
  have : IsIso (j ≫ sigmaSpec (fun _ : G ↦ CommRingCat.of B)) := he.symm ▸ inferInstance
  exact IsIso.of_isIso_comp_left j _

end AllCharacteristics
