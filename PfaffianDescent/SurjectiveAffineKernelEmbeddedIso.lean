import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! SOURCE ONLY / UNVERIFIED. Complete affine kernels classify actual
embedded schemes up to an isomorphism over the fixed ambient scheme.
The open chart is used only through its monomorphism. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

theorem surjectiveAffineAlgMaps_sameKernel_iff_overIso
    {K R A B : Type u} [CommRing K] [CommRing R] [CommRing A] [CommRing B]
    [Algebra K R] [Algebra K A] [Algebra K B]
    (phi₁ : R →ₐ[K] A) (phi₂ : R →ₐ[K] B)
    (hphi₁ : Function.Surjective phi₁) (hphi₂ : Function.Surjective phi₂) :
    RingHom.ker phi₁.toRingHom = RingHom.ker phi₂.toRingHom ↔
      ∃ e : Spec (.of A) ≅ Spec (.of B),
        e.hom ≫ Spec.map (CommRingCat.ofHom phi₂.toRingHom) =
          Spec.map (CommRingCat.ofHom phi₁.toRingHom) := by
  constructor
  · intro hker
    let f := AlgHom.liftOfSurjective phi₁ hphi₁ phi₂ hker.le
    let g := AlgHom.liftOfSurjective phi₂ hphi₂ phi₁ hker.symm.le
    have hfg : f.comp g = AlgHom.id K B := by
      apply AlgHom.ext
      intro z
      obtain ⟨r, rfl⟩ := hphi₂ z
      change (AlgHom.liftOfSurjective phi₁ hphi₁ phi₂ hker.le)
        ((AlgHom.liftOfSurjective phi₂ hphi₂ phi₁ hker.symm.le) (phi₂ r)) = phi₂ r
      rw [AlgHom.liftOfSurjective_apply, AlgHom.liftOfSurjective_apply]
    have hgf : g.comp f = AlgHom.id K A := by
      apply AlgHom.ext
      intro z
      obtain ⟨r, rfl⟩ := hphi₁ z
      change (AlgHom.liftOfSurjective phi₂ hphi₂ phi₁ hker.symm.le)
        ((AlgHom.liftOfSurjective phi₁ hphi₁ phi₂ hker.le) (phi₁ r)) = phi₁ r
      rw [AlgHom.liftOfSurjective_apply, AlgHom.liftOfSurjective_apply]
    let e := AlgEquiv.ofAlgHom f g hfg hgf
    have he (r : R) : e (phi₁ r) = phi₂ r :=
      AlgHom.liftOfSurjective_apply phi₁ hphi₁ phi₂ hker.le r
    let eSpec := Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.symm.op
    refine ⟨eSpec, ?_⟩
    have hcomp : CommRingCat.ofHom phi₂.toRingHom ≫
        CommRingCat.ofHom e.symm.toRingHom = CommRingCat.ofHom phi₁.toRingHom := by
      ext r
      change e.symm (phi₂ r) = phi₁ r
      apply e.injective
      rw [e.apply_symm_apply, he]
    change Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ _ = _
    rw [← Spec.map_comp, hcomp]
  · rintro ⟨e, he⟩
    let f := (Spec.preimage e.hom).hom
    let g := (Spec.preimage e.inv).hom
    have hgf : g.comp f = RingHom.id B := by
      have hcat : Spec.preimage e.hom ≫ Spec.preimage e.inv = 𝟙 (CommRingCat.of B) := by
        rw [← Spec.preimage_comp, e.inv_hom_id, Spec.preimage_id]
      exact congrArg CommRingCat.Hom.hom hcat
    have hf : Function.Injective f := by
      intro a b hab
      have h := congrArg g hab
      simpa only [← RingHom.comp_apply, hgf, RingHom.id_apply] using h
    have hcomp : f.comp phi₂.toRingHom = phi₁.toRingHom := by
      have hcat : CommRingCat.ofHom phi₂.toRingHom ≫ Spec.preimage e.hom =
          CommRingCat.ofHom phi₁.toRingHom := by
        apply Spec.map_injective
        rw [Spec.map_comp, Spec.map_preimage, he]
      exact congrArg CommRingCat.Hom.hom hcat
    apply Ideal.ext
    intro r
    change phi₁.toRingHom r = 0 ↔ phi₂.toRingHom r = 0
    rw [← RingHom.congr_fun hcomp r]
    change f (phi₂ r) = 0 ↔ phi₂ r = 0
    constructor
    · intro h
      exact hf (h.trans (map_zero f).symm)
    · intro h
      rw [h, map_zero]

theorem surjectiveAffineAlgMaps_sameKernel_iff_originalEmbeddedIso
    {K R A B : Type u} [CommRing K] [CommRing R] [CommRing A] [CommRing B]
    [Algebra K R] [Algebra K A] [Algebra K B]
    (phi₁ : R →ₐ[K] A) (phi₂ : R →ₐ[K] B)
    (hphi₁ : Function.Surjective phi₁) (hphi₂ : Function.Surjective phi₂)
    {X : Scheme.{u}} (j : Spec (.of R) ⟶ X) [Mono j] :
    RingHom.ker phi₁.toRingHom = RingHom.ker phi₂.toRingHom ↔
      ∃ e : Spec (.of A) ≅ Spec (.of B),
        e.hom ≫ (Spec.map (CommRingCat.ofHom phi₂.toRingHom) ≫ j) =
          Spec.map (CommRingCat.ofHom phi₁.toRingHom) ≫ j := by
  rw [surjectiveAffineAlgMaps_sameKernel_iff_overIso phi₁ phi₂ hphi₁ hphi₂]
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e, by rw [← Category.assoc, he]⟩
  · rintro ⟨e, he⟩
    refine ⟨e, (cancel_mono j).mp ?_⟩
    simpa only [Category.assoc] using he

end PfaffianDescent
