import AllCharacteristics.SmoothPointLifting
import AllCharacteristics.SurjectiveResiduePresentation

/-!
# Lifting a smooth point into a complete local algebra

Base change turns a field-valued point into a residue-field point over the
complete local target algebra. Smoothness then gives an actual scheme
morphism with exactly the prescribed reduction and coefficient map.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
namespace AllCharacteristics
universe u

/-- A point of a smooth scheme lifts into any complete local coefficient
algebra presenting its field of definition as residue field. -/
theorem lift_smooth_point_to_complete_local_algebra
    {R A L : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A] [Field L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Smooth f]
    (d : A →+* L) (hd : Function.Surjective d)
    (q : Spec (.of L) ⟶ X)
    (hq : q ≫ f = Spec.map (CommRingCat.ofHom (d.comp (algebraMap R A)))) :
    ∃ s : Spec (.of A) ⟶ X,
      s ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)) ∧
      Spec.map (CommRingCat.ofHom d) ≫ s = q := by
  let a := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let qA : Spec (.of L) ⟶ pullback f a := pullback.lift q
    (Spec.map (CommRingCat.ofHom d)) (by rw [← Spec.map_comp]; exact hq)
  let e := residueEquivOfSurjective d hd
  let ei := Spec.map (CommRingCat.ofHom e.symm.toRingHom)
  have : IsIso ei := isIso_SpecMap_iff.mpr e.symm.bijective
  have he : CommRingCat.ofHom d ≫ CommRingCat.ofHom e.symm.toRingHom =
      CommRingCat.ofHom (residue A) := by
    ext x
    exact e.symm_apply_eq.mpr (residueEquivOfSurjective_residue d hd x).symm
  let q0 := ei ≫ qA
  have hq0 : q0 ≫ pullback.snd f a = Spec.map (CommRingCat.ofHom (residue A)) := by
    change ei ≫ qA ≫ pullback.snd f a = _
    rw [pullback.lift_snd]
    change Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom d) = _
    rw [← Spec.map_comp, he]
  obtain ⟨sA, hsA, hred⟩ := lift_smooth_residue_point (pullback.snd f a) q0 hq0
  refine ⟨sA ≫ pullback.fst f a, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hsA, Category.id_comp]
  · apply (cancel_epi ei).mp
    have hleft : ei ≫ Spec.map (CommRingCat.ofHom d) =
        Spec.map (CommRingCat.ofHom (residue A)) := by
      change Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom d) = _
      rw [← Spec.map_comp, he]
    rw [← Category.assoc ei, hleft, ← Category.assoc, hred]
    change (ei ≫ qA) ≫ pullback.fst f a = ei ≫ q
    rw [Category.assoc, pullback.lift_fst]

end AllCharacteristics
