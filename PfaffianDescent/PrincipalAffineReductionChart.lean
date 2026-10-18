import PfaffianDescent.HilbertBurchLocalizationSurjection318
import PfaffianDescent.ActualAffineTensorFiber174

/-!
A chosen lift of the principal
denominator constructs the genuine upstairs/downstairs affine chart
square.  Surjectivity and the entire reduction kernel are derived from
the original reduction, rather than supplied for the new neighborhood.
-/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option autoImplicit false

theorem actualAwayMap_isPullback001
    {A' A : Type u} [CommRing A'] [CommRing A]
    (π : A' →+* A) (hπ : Function.Surjective π)
    (r' : A') (r : A) (hr : π r' = r) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (actualAwayMap022 π r' r hr)))
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away r))))
      (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away r'))))
      (Spec.map (CommRingCat.ofHom π)) := by
  have hcomm : (actualAwayMap022 π r' r hr).comp
      (algebraMap A' (Localization.Away r')) =
      (algebraMap A (Localization.Away r)).comp π := by
    ext x
    exact actualAwayMap_algebraMap022 π r' r hr x
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (AllCharacteristics.isPushout_of_surjective_of_ker_map _ _ _ _ hπ
      (actualAwayMap_surjective022 π hπ r' r hr) hcomm
      (actualAwayMap_ker022 π r' r hr))

theorem principalAffineReductionChart001
    {B A' A : Type u} [CommRing B] [CommRing A'] [CommRing A]
    [Algebra B A'] [Algebra B A]
    {X X0 : Scheme.{u}} (F : X ⟶ Spec (.of B)) (d : X0 ⟶ X)
    (a : Spec (.of A') ⟶ X) [IsOpenImmersion a]
    (ha : a ≫ F = Spec.map (CommRingCat.ofHom (algebraMap B A')))
    (π : A' →ₐ[B] A) (hπ : Function.Surjective π)
    (I : Ideal B) (hker : RingHom.ker π.toRingHom = I.map (algebraMap B A'))
    (a0 : Spec (.of A) ⟶ X0)
    (Hchart : IsPullback (Spec.map (CommRingCat.ofHom π.toRingHom)) a0 a d)
    (r' : A') (r : A) (hr : π r' = r) :
    let ar := Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away r'))) ≫ a
    let a0r := Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away r))) ≫ a0
    let πr := actualAwayAlgHom022 π r' r hr
    IsOpenImmersion ar ∧
      ar ≫ F = Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away r'))) ∧
      IsPullback (Spec.map (CommRingCat.ofHom πr.toRingHom)) a0r ar d ∧
      Function.Surjective πr ∧
      RingHom.ker πr.toRingHom = I.map (algebraMap B (Localization.Away r')) := by
  let l := Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away r')))
  let l0 := Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away r)))
  letI : IsOpenImmersion l := IsOpenImmersion.of_isLocalization r'
  refine ⟨inferInstance, ?_, ?_, actualAwayMap_surjective022 π.toRingHom hπ r' r hr,
    actualAwayMap_coefficient_ker022 I π.toRingHom hker r' r hr⟩
  · change (l ≫ a) ≫ F = _
    rw [Category.assoc, ha, ← Spec.map_comp]
    rfl
  · exact (actualAwayMap_isPullback001 π.toRingHom hπ r' r hr).paste_vert Hchart

end PfaffianDescent
end
