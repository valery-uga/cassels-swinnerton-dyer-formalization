import AllCharacteristics.ProjectivePoints
import AllCharacteristics.UniversalHomogeneous
import AllCharacteristics.SchemeSpecialization

/-!
# Points of fibers of the universal homogeneous family

These results describe actual scheme-theoretic fibers at the level of their
field-valued sections. In particular the coefficient-specialization identity is
connected to points of the fiber of the proper universal family.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u

/-- A section of a base-changed fiber is equivalent to a point of the original
scheme over the given coefficient map. -/
theorem fiber_section_iff_pointOver {R k : Type u} [CommRing R] [CommRing k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (b : R →+* k) :
    (∃ q : Spec (.of k) ⟶ pullback f (Spec.map (CommRingCat.ofHom b)),
      q ≫ pullback.snd f (Spec.map (CommRingCat.ofHom b)) = 𝟙 _) ↔ HasPointOver f b := by
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨q ≫ pullback.fst f (Spec.map (CommRingCat.ofHom b)), ?_⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc, hq, Category.id_comp]
  · rintro ⟨q, hq⟩
    refine ⟨pullback.lift q (𝟙 _) ?_, pullback.lift_snd _ _ _⟩
    simpa only [Category.id_comp] using hq

/-- A field-valued fiber of a homogeneous hypersurface has a section exactly
when its specialized homogeneous equation has a nonzero solution. -/
theorem hypersurface_fiber_section_iff_coordinates
    {R k : Type u} [CommRing R] [Field k] {σ : Type}
    (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d) (b : R →+* k) :
    (∃ q : Spec (.of k) ⟶ pullback (HomogeneousProjective.hypersurfaceToBase p hp)
        (Spec.map (CommRingCat.ofHom b)),
      q ≫ pullback.snd (HomogeneousProjective.hypersurfaceToBase p hp)
        (Spec.map (CommRingCat.ofHom b)) = 𝟙 _) ↔
      ∃ x : σ → k, x ≠ 0 ∧ p.eval₂ b x = 0 :=
  (fiber_section_iff_pointOver (HomogeneousProjective.hypersurfaceToBase p hp) b).trans
    (HomogeneousProjective.hypersurface_has_point_iff_coordinates b p hp)

/-- The fiber of the proper universal homogeneous family at the coefficients
of a homogeneous polynomial has a field-valued section exactly when that
polynomial has a nonzero solution. No characteristic assumption is used. -/
theorem universal_fiber_section_iff_coordinates
    {B k : Type u} [CommRing B] [Field k] {σ : Type} [Finite σ]
    (f : B →+* k) (p : MvPolynomial σ k) {d : ℕ} (hp : p.IsHomogeneous d) :
    let b := MvPolynomial.eval₂Hom f (fun m : UniversalHomogeneous.Monomials σ d ↦ p.coeff m.1)
    (∃ q : Spec (.of k) ⟶ pullback (UniversalHomogeneous.familyToCoefficients B σ d)
        (Spec.map (CommRingCat.ofHom b)),
      q ≫ pullback.snd (UniversalHomogeneous.familyToCoefficients B σ d)
        (Spec.map (CommRingCat.ofHom b)) = 𝟙 _) ↔
      ∃ x : σ → k, x ≠ 0 ∧ MvPolynomial.eval x p = 0 := by
  dsimp only
  refine (hypersurface_fiber_section_iff_coordinates (UniversalHomogeneous.form σ d B)
    (UniversalHomogeneous.form_isHomogeneous σ d B)
    (MvPolynomial.eval₂Hom f (fun m : UniversalHomogeneous.Monomials σ d ↦ p.coeff m.1))).trans ?_
  apply exists_congr
  intro x
  apply and_congr_right
  intro _
  rw [MvPolynomial.eval₂_eq_eval_map, UniversalHomogeneous.map_form_eq f p hp]

end AllCharacteristics
