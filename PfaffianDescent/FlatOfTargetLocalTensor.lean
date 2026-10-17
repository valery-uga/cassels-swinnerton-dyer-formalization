import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Flatness from localization on the base

This is the algebraic descent step for flatness from the local spectra of
target points. It states the precise tensor-product condition obtained by
base-changing an affine morphism along the map to a local ring of its base.
-/

namespace PfaffianDescent

open TensorProduct
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

/-- If an algebra becomes flat after tensoring with the local ring at every
maximal ideal of its base, it is flat over that base. -/
theorem moduleFlat_of_flat_targetLocalTensor
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      Module.Flat (Localization P.primeCompl)
        (Localization P.primeCompl ⊗[R] S)) : Module.Flat R S := by
  apply Module.flat_of_localized_maximal S
  intro P hP
  letI : Module.Flat (Localization P.primeCompl)
      (Localization P.primeCompl ⊗[R] S) := h P
  haveI : Module.Flat (Localization P.primeCompl)
      (LocalizedModule P.primeCompl S) :=
    Module.Flat.of_linearEquiv
      (LocalizedModule.equivTensorProduct P.primeCompl S)
  exact Module.Flat.trans R (Localization P.primeCompl) _

/-- Affine flatness descends from the canonical localizations of the target.
The geometric input is flatness of the actual scheme-theoretic base change. -/
theorem flat_specMap_of_flat_targetLocalBaseChanges
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      Flat (pullback.fst
        (Spec.map (CommRingCat.ofHom
          (algebraMap R (Localization P.primeCompl))))
        (Spec.map (CommRingCat.ofHom (algebraMap R S))))) :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  apply Flat.SpecMap_iff.mpr
  apply RingHom.flat_algebraMap_iff.mpr
  apply moduleFlat_of_flat_targetLocalTensor
  intro P hP
  have hmap : Flat (Spec.map (CommRingCat.ofHom
      (algebraMap (Localization P.primeCompl)
        (Localization P.primeCompl ⊗[R] S)))) := by
    rw [← pullbackSpecIso_inv_fst' R (Localization P.primeCompl) S]
    exact inferInstance
  exact RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp hmap)

/-- The same affine criterion in the orientation used when base-changing
a morphism to its target's local spectrum. -/
theorem flat_specMap_of_flat_targetLocalFibres
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      Flat (pullback.snd
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (Spec.map (CommRingCat.ofHom
          (algebraMap R (Localization P.primeCompl)))))) :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  apply flat_specMap_of_flat_targetLocalBaseChanges
  intro P hP
  haveI : Flat (pullback.snd
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom
        (algebraMap R (Localization P.primeCompl))))) := h P
  rw [← pullbackSymmetry_inv_comp_snd]
  infer_instance

/-- Flatness of a base-changed morphism persists when its source is
restricted by an open immersion. -/
theorem flat_pullback_snd_comp_openSource
    {W X Y T : Scheme.{u}} (i : W ⟶ X) [IsOpenImmersion i]
    (f : X ⟶ Y) (s : T ⟶ Y)
    (h : Flat (pullback.snd f s)) :
    Flat (pullback.snd (i ≫ f) s) := by
  let e := pullbackRightPullbackFstIso f s i
  haveI : Flat (pullback.snd f s) := h
  haveI : Flat (pullback.snd i (pullback.fst f s)) := inferInstance
  have hcomp : Flat (e.hom ≫ pullback.snd (i ≫ f) s) := by
    rw [pullbackRightPullbackFstIso_hom_snd]
    infer_instance
  haveI : Flat e.inv := inferInstance
  have hres : Flat (e.inv ≫ (e.hom ≫ pullback.snd (i ≫ f) s)) :=
    inferInstance
  simpa only [← Category.assoc, Iso.inv_hom_id,
    Category.id_comp] using hres

/-- Reassociate a flat target base change through an intermediate base
scheme. -/
theorem flat_pullback_snd_targetComp
    {X Y V T : Scheme.{u}} (f : X ⟶ Y) (g : V ⟶ Y)
    (s : T ⟶ V) (h : Flat (pullback.snd f (s ≫ g))) :
    Flat (pullback.snd (pullback.snd f g) s) := by
  let e := pullbackLeftPullbackSndIso f g s
  haveI : Flat (pullback.snd f (s ≫ g)) := h
  have hcomp : Flat (e.hom ≫ pullback.snd f (s ≫ g)) := inferInstance
  rw [pullbackLeftPullbackSndIso_hom_snd] at hcomp
  exact hcomp

/-- An affine-source morphism to an affine base is flat if all its target
localizations are flat, without choosing a literal `Spec` presentation of
the source. -/
theorem flat_affineSource_toSpec_of_flat_targetLocalFibres
    {R : Type u} [CommRing R] {X : Scheme.{u}} [IsAffine X]
    (f : X ⟶ Spec (.of R))
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      Flat (pullback.snd f
        (Spec.map (CommRingCat.ofHom
          (algebraMap R (Localization P.primeCompl)))))) : Flat f := by
  let e := X.isoSpec
  let φ : R →+* Γ(X, ⊤) := (Spec.preimage (e.inv ≫ f)).hom
  letI : Algebra R Γ(X, ⊤) := φ.toAlgebra
  have hmap : Flat (Spec.map (CommRingCat.ofHom φ)) := by
    apply flat_specMap_of_flat_targetLocalFibres
    intro P hP
    have hf := flat_pullback_snd_comp_openSource e.inv f
      (Spec.map (CommRingCat.ofHom
        (algebraMap R (Localization P.primeCompl)))) (h P)
    change Flat (pullback.snd (Spec.map (Spec.preimage (e.inv ≫ f)))
      (Spec.map (CommRingCat.ofHom
        (algebraMap R (Localization P.primeCompl)))))
    rw [Spec.map_preimage]
    exact hf
  have hcomp : Flat (e.hom ≫ (e.inv ≫ f)) := by
    haveI : Flat (e.inv ≫ f) := by
      rw [← Spec.map_preimage (e.inv ≫ f)]
      exact hmap
    infer_instance
  simpa only [← Category.assoc, Iso.hom_inv_id,
    Category.id_comp] using hcomp

/-- A morphism to an affine base is flat when all its target localizations
are flat, with no affine assumption on its source. -/
theorem flat_toSpec_of_flat_targetLocalFibres
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R))
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      Flat (pullback.snd f
        (Spec.map (CommRingCat.ofHom
          (algebraMap R (Localization P.primeCompl)))))) : Flat f := by
  have : IsZariskiLocalAtSource (@Flat) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Flat)
  apply (IsZariskiLocalAtSource.iff_of_openCover (P := @Flat) X.affineCover).mpr
  intro i
  apply flat_affineSource_toSpec_of_flat_targetLocalFibres
  intro P hP
  exact flat_pullback_snd_comp_openSource (X.affineCover.f i) f
    (Spec.map (CommRingCat.ofHom
      (algebraMap R (Localization P.primeCompl)))) (h P)

/-- Flatness of a target fibre is invariant under replacing the target by
an isomorphic base scheme. -/
theorem flat_pullback_snd_postcompIso
    {X Y Z T : Scheme.{u}} (e : Y ≅ Z) (f : X ⟶ Y)
    (s : T ⟶ Z)
    (h : Flat (pullback.snd f (s ≫ e.inv))) :
    Flat (pullback.snd (f ≫ e.hom) s) := by
  let m := pullback.map f (s ≫ e.inv) (f ≫ e.hom) s
    (𝟙 X) (𝟙 T) e.hom (by simp) (by simp)
  let em := asIso m
  have hm : em.hom ≫ pullback.snd (f ≫ e.hom) s =
      pullback.snd f (s ≫ e.inv) := by
    simp only [em, m, asIso_hom, pullback.map,
      pullback.lift_snd, Category.comp_id]
  haveI : Flat (pullback.snd f (s ≫ e.inv)) := h
  have hcomp : Flat (em.inv ≫ (em.hom ≫ pullback.snd (f ≫ e.hom) s)) := by
    rw [hm]
    infer_instance
  simpa only [← Category.assoc, Iso.inv_hom_id,
    Category.id_comp] using hcomp

/-- The target-local flatness criterion for an affine target presented as
an arbitrary affine scheme. -/
theorem flat_toAffineTarget_of_flat_targetLocalFibres
    {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y)
    (h : ∀ (P : Ideal Γ(Y, ⊤)) [P.IsMaximal],
      Flat (pullback.snd f
        (Spec.map (CommRingCat.ofHom
          (algebraMap Γ(Y, ⊤) (Localization P.primeCompl))) ≫
            Y.isoSpec.inv))) : Flat f := by
  let e := Y.isoSpec
  have hspec : Flat (f ≫ e.hom) := by
    apply flat_toSpec_of_flat_targetLocalFibres
    intro P hP
    exact flat_pullback_snd_postcompIso e f
      (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(Y, ⊤) (Localization P.primeCompl)))) (h P)
  haveI : Flat (f ≫ e.hom) := hspec
  have hres : Flat ((f ≫ e.hom) ≫ e.inv) := inferInstance
  simpa only [Category.assoc, Iso.hom_inv_id,
    Category.comp_id] using hres

/-- Flatness of a scheme morphism can be checked after base change to the
local spectra at maximal ideals of each target affine chart. -/
theorem flat_of_flat_targetAffineLocalFibres
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ i : Y.affineCover.I₀,
      ∀ (P : Ideal Γ(Y.affineCover.X i, ⊤)) [P.IsMaximal],
        Flat (pullback.snd f
          ((Spec.map (CommRingCat.ofHom
              (algebraMap Γ(Y.affineCover.X i, ⊤)
                (Localization P.primeCompl))) ≫
            (Y.affineCover.X i).isoSpec.inv) ≫ Y.affineCover.f i))) :
    Flat f := by
  have : IsZariskiLocalAtTarget (@Flat) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget
      (P := @Flat) (Q := RingHom.Flat)
  apply (IsZariskiLocalAtTarget.iff_of_openCover
    (P := @Flat) Y.affineCover).mpr
  intro i
  apply flat_toAffineTarget_of_flat_targetLocalFibres
  intro P hP
  exact flat_pullback_snd_targetComp f (Y.affineCover.f i)
    (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(Y.affineCover.X i, ⊤)
        (Localization P.primeCompl))) ≫
      (Y.affineCover.X i).isoSpec.inv) (h i P)

end PfaffianDescent
