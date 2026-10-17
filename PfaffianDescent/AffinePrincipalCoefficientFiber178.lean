import AllCharacteristics.AffineLocalizationPullback
import Mathlib.RingTheory.Localization.BaseChange

/-! SOURCE ONLY / UNVERIFIED178. Principal affine neighborhoods commute
with the ORIGINAL coefficient fiber. Native localization/pullback results
are reused; the whole reduction and scalar maps are pinned down. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable {R S A' : Type u} [CommRing R] [CommRing S] [CommRing A']
  [Algebra R S] [Algebra R A']

/-- Native base-change equivalence for the actual lifted principal open. -/
def affinePrincipalCoefficientFiberEquiv178 (t' : A') :
    S ⊗[R] Localization.Away t' ≃ₐ[S]
      Localization.Away ((Algebra.TensorProduct.includeRight : A' →ₐ[R] S ⊗[R] A') t') :=
  IsLocalization.Away.tensorProductEquivTMulRight R S t' (Localization.Away t')

lemma affinePrincipalCoefficientFiberEquiv178_tmul
    (t' a' : A') (s : S) :
    affinePrincipalCoefficientFiberEquiv178 (R := R) (S := S) t'
      (s ⊗ₜ[R] algebraMap A' (Localization.Away t') a') =
    algebraMap (S ⊗[R] A')
      (Localization.Away ((Algebra.TensorProduct.includeRight : A' →ₐ[R] S ⊗[R] A') t'))
      (s ⊗ₜ[R] a') :=
  IsLocalization.Away.tensorProductEquivTMulRight_tmul
    (R := R) (S := S) (A := A') t' (Localization.Away t') s a'

/-- The ENTIRE upstairs localized reduction is the literal awayMap,
not merely a map agreeing on the lifted principal element. -/
lemma affinePrincipalCoefficientFiberEquiv178_comp_reduction
    (t' : A') :
    (affinePrincipalCoefficientFiberEquiv178 (R := R) (S := S) t').toRingHom.comp
      (Algebra.TensorProduct.includeRight : Localization.Away t' →ₐ[R]
        S ⊗[R] Localization.Away t').toRingHom =
    Localization.awayMap
      (Algebra.TensorProduct.includeRight : A' →ₐ[R] S ⊗[R] A').toRingHom t' := by
  apply IsLocalization.ringHom_ext (Submonoid.powers t')
  apply RingHom.ext
  intro a'
  change affinePrincipalCoefficientFiberEquiv178 (R := R) (S := S) t'
      (1 ⊗ₜ[R] algebraMap A' (Localization.Away t') a') =
    Localization.awayMap
      (Algebra.TensorProduct.includeRight : A' →ₐ[R] S ⊗[R] A').toRingHom t'
      (algebraMap A' (Localization.Away t') a')
  rw [affinePrincipalCoefficientFiberEquiv178_tmul]
  exact (DFunLike.congr_fun (AllCharacteristics.awayMap_comp_algebraMap
    (Algebra.TensorProduct.includeRight : A' →ₐ[R] S ⊗[R] A').toRingHom t') a').symm

/-- The original S scalar map is preserved on EVERY coefficient. -/
lemma affinePrincipalCoefficientFiberEquiv178_comp_scalar
    (t' : A') :
    (affinePrincipalCoefficientFiberEquiv178 (R := R) (S := S) t').toRingHom.comp
      (algebraMap S (S ⊗[R] Localization.Away t')) =
    algebraMap S
      (Localization.Away ((Algebra.TensorProduct.includeRight : A' →ₐ[R] S ⊗[R] A') t')) :=
  (affinePrincipalCoefficientFiberEquiv178 (R := R) (S := S) t').toAlgHom.comp_algebraMap

/-- The literal downstairs principal neighborhood is the actual
coefficient fiber of the literal upstairs principal neighborhood. -/
lemma affinePrincipalCoefficientFiber178_isPullback
    (t' : A') :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Localization.awayMap
        (Algebra.TensorProduct.includeRight : A' →ₐ[R] S ⊗[R] A').toRingHom t')))
      (Spec.map (CommRingCat.ofHom (algebraMap S
        (Localization.Away ((Algebra.TensorProduct.includeRight : A' →ₐ[R] S ⊗[R] A') t')))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away t'))))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  let pi : A' →+* S ⊗[R] A' :=
    (Algebra.TensorProduct.includeRight : A' →ₐ[R] S ⊗[R] A').toRingHom
  have hAmbient : IsPullback
      (Spec.map (CommRingCat.ofHom pi))
      (Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A'))))
      (Spec.map (CommRingCat.ofHom (algebraMap R A')))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
    isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct R S A').flip
  have h := (AllCharacteristics.isPullback_Spec_awayMap pi t').flip.paste_vert hAmbient
  have hS : Spec.map (CommRingCat.ofHom
      (algebraMap (S ⊗[R] A') (Localization.Away (pi t')))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A'))) =
      Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (pi t')))) := by
    rw [← Spec.map_comp]
    rfl
  have hR : Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away t'))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A')) =
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away t'))) := by
    rw [← Spec.map_comp]
    rfl
  rw [hS, hR] at h
  exact h

/-- For the ORIGINAL prescribed downstairs principal parameter t, choose
its actual upstairs lift and recover that SAME neighborhood, with whole
ambient-reduction and original coefficient maps. No new-neighborhood,
base-change, reduction, or flatness outcome certificate is supplied. -/
lemma exists_prescribedPrincipalCoefficientFiber178
    (hRS : Function.Surjective (algebraMap R S)) (t : S ⊗[R] A') :
    ∃ (t' : A') (e : S ⊗[R] Localization.Away t' ≃ₐ[S] Localization.Away t)
      (sigma : Localization.Away t' →+* Localization.Away t),
      (Algebra.TensorProduct.includeRight : A' →ₐ[R] S ⊗[R] A') t' = t ∧
      e.toRingHom.comp
        (Algebra.TensorProduct.includeRight : Localization.Away t' →ₐ[R]
          S ⊗[R] Localization.Away t').toRingHom = sigma ∧
      e.toRingHom.comp (algebraMap S (S ⊗[R] Localization.Away t')) =
        algebraMap S (Localization.Away t) ∧
      sigma.comp (algebraMap A' (Localization.Away t')) =
        (algebraMap (S ⊗[R] A') (Localization.Away t)).comp
          (Algebra.TensorProduct.includeRight : A' →ₐ[R] S ⊗[R] A').toRingHom ∧
      IsPullback (Spec.map (CommRingCat.ofHom sigma))
        (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away t))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away t'))))
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  obtain ⟨t', rfl⟩ := Algebra.TensorProduct.includeRight_surjective A' hRS t
  exact ⟨t', affinePrincipalCoefficientFiberEquiv178 t',
    Localization.awayMap
      (Algebra.TensorProduct.includeRight : A' →ₐ[R] S ⊗[R] A').toRingHom t',
    rfl, affinePrincipalCoefficientFiberEquiv178_comp_reduction t',
    affinePrincipalCoefficientFiberEquiv178_comp_scalar t',
    AllCharacteristics.awayMap_comp_algebraMap
      (Algebra.TensorProduct.includeRight : A' →ₐ[R] S ⊗[R] A').toRingHom t',
    affinePrincipalCoefficientFiber178_isPullback t'⟩

end PfaffianDescent
