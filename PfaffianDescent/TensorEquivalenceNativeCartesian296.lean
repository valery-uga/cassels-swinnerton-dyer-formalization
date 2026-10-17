import Mathlib.AlgebraicGeometry.Pullbacks

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
universe u
variable {C S Q T : Type u} [CommRing C] [CommRing S] [CommRing Q] [CommRing T]
variable [Algebra C S] [Algebra C Q] [Algebra S T]

/-- The genuine right-hand ring map induced by a proved tensor target equivalence. -/
def tensorEquivalenceRightRingMap296 (e : S ⊗[C] Q ≃ₐ[S] T) : Q →+* T :=
  e.toRingHom.comp (Algebra.TensorProduct.includeRight (R := C) (A := S) (B := Q)).toRingHom

lemma tensorEquivalenceNativePushout296 (e : S ⊗[C] Q ≃ₐ[S] T) :
    IsPushout (CommRingCat.ofHom (algebraMap C S)) (CommRingCat.ofHom (algebraMap C Q))
      (CommRingCat.ofHom (algebraMap S T)) (CommRingCat.ofHom (tensorEquivalenceRightRingMap296 e)) := by
  refine (CommRingCat.isPushout_tensorProduct C S Q).of_iso
    (Iso.refl (CommRingCat.of C)) (Iso.refl (CommRingCat.of S)) (Iso.refl (CommRingCat.of Q))
    e.toRingEquiv.toCommRingCatIso ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro s
    exact e.commutes s
  · rfl

/-- Spec turns the constructed native pushout into the actual Cartesian scalar-extension square. -/
lemma tensorEquivalenceNativeSpecCartesian296 (e : S ⊗[C] Q ≃ₐ[S] T) :
    IsPullback (Spec.map (CommRingCat.ofHom (tensorEquivalenceRightRingMap296 e)))
      (Spec.map (CommRingCat.ofHom (algebraMap S T)))
      (Spec.map (CommRingCat.ofHom (algebraMap C Q)))
      (Spec.map (CommRingCat.ofHom (algebraMap C S))) :=
  (AlgebraicGeometry.isPullback_SpecMap_of_isPushout
    (CommRingCat.ofHom (algebraMap C S)) (CommRingCat.ofHom (algebraMap C Q))
    (CommRingCat.ofHom (algebraMap S T)) (CommRingCat.ofHom (tensorEquivalenceRightRingMap296 e))
    (tensorEquivalenceNativePushout296 e)).flip

end PfaffianDescent
