import AllCharacteristics.ConfigurationVoisinDegreeTenSteps
import AllCharacteristics.VoisinDegreeTenReduction
import AllCharacteristics.CubicSurfaceMain

/-!
# Packaging collision-aware endpoint families as Voisin's degree-ten input

This module closes the interface gap between geometric moving constructions
and the characteristic-zero reduction theorem.  The special fibers may be
nonreduced, so the input is expressed directly as finite-flat endpoint
families.  Their geometric existence remains an input; this theorem only
converts those families into the formulation used by the arithmetic.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits PfaffianDescent
namespace AllCharacteristics
namespace HomogeneousProjective

universe u

/-- Uniform collision-aware endpoint-family constructions on cubic hypersurfaces
give the family-level degree-ten geometry required by Voisin's reduction. -/
theorem voisinDegreeTenFamilyGeometryFor_of_configurationCurveSteps
    {k : Type u} [Field k] [CharZero k]
    (curves : ∀ (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3), p ≠ 0 →
      Smooth (hypersurfaceToBase p hp) →
      ∀ h : EffectiveZeroCycle (hypersurface p hp),
        EffectiveZeroCycle.degree (hypersurfaceToBase p hp) h = 3 →
        VoisinDegreeTenConfigurationCurveSteps
          (A := CoordinateRing (equationIdeal p hp)) (K := k)
          (grading (equationIdeal p hp))
          (show Proj (grading (equationIdeal p hp)) ⟶ Spec (.of k) from
            toBase (equationIdeal p hp)) h) :
    VoisinDegreeTenFamilyGeometryFor k := by
  intro p hp hne hs
  obtain ⟨h, hh⟩ := hypersurface_exists_effective_degree_three
    (k := k) (n := 4) 0 1 (by decide) p hp
  let I := equationIdeal p hp
  have hcurve := curves p hp hne hs h hh
  exact ⟨h, hh, voisinDegreeTenFamilySteps_of_configurationCurveSteps
    (A := CoordinateRing I) (K := k)
    (grading I) (show Proj (grading I) ⟶ Spec (.of k) from toBase I) h hcurve⟩

/- The same reduction can consume explicit curves in the full ordered relative
   powers.  The conversion inserts the collision-aware disjoint-union family
   before passing to the degree-ten arithmetic. -/
theorem voisinDegreeTenFamilyGeometryFor_of_orderedTupleCurveSteps
    {k : Type u} [Field k] [CharZero k]
    (curves : ∀ (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3), p ≠ 0 →
      Smooth (hypersurfaceToBase p hp) →
      ∀ h : EffectiveZeroCycle (hypersurface p hp),
        EffectiveZeroCycle.degree (hypersurfaceToBase p hp) h = 3 →
        VoisinDegreeTenOrderedTupleCurveSteps
          (K := k)
          (grading (equationIdeal p hp))
          (show Proj (grading (equationIdeal p hp)) ⟶ Spec (.of k) from
            toBase (equationIdeal p hp)) h) :
    VoisinDegreeTenFamilyGeometryFor k := by
  apply voisinDegreeTenFamilyGeometryFor_of_configurationCurveSteps
  intro p hp hne hs h hh
  exact voisinDegreeTenConfigurationCurveSteps_of_orderedTupleCurveSteps
    (K := k)
    (grading (equationIdeal p hp))
    (show Proj (grading (equationIdeal p hp)) ⟶ Spec (.of k) from
      toBase (equationIdeal p hp)) h (curves p hp hne hs h hh)

end HomogeneousProjective
end AllCharacteristics

namespace AllCharacteristics
namespace HomogeneousProjective

/-- Coray's alternative together with uniform endpoint families yields the
characteristic-zero rational section conclusion directly. -/
theorem charZero_cubic_section_of_zeroCycle_degree_one_of_coray_and_configurationCurveSteps
    {k : Type u} [Field k] [CharZero k]
    (coray : CorayDegreeOneFourOrTenFor k)
    (curves : ∀ (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3), p ≠ 0 →
      Smooth (hypersurfaceToBase p hp) →
      ∀ h : EffectiveZeroCycle (hypersurface p hp),
        EffectiveZeroCycle.degree (hypersurfaceToBase p hp) h = 3 →
        VoisinDegreeTenConfigurationCurveSteps
          (A := CoordinateRing (equationIdeal p hp)) (K := k)
          (grading (equationIdeal p hp))
          (show Proj (grading (equationIdeal p hp)) ⟶ Spec (.of k) from
            toBase (equationIdeal p hp)) h)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ a : Spec (.of k) ⟶ hypersurface p hp,
      a ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  exact cubic_section_of_zeroCycle_degree_one_of_coray_and_degree_ten_geometry_direct
    coray (voisinDegreeTenGeometryFor_of_familyGeometryFor
      (voisinDegreeTenFamilyGeometryFor_of_configurationCurveSteps curves))
    p hp hne z hz

end HomogeneousProjective
end AllCharacteristics

namespace AllCharacteristics
namespace HomogeneousProjective

/-- The all-characteristics reduction can consume uniform endpoint-family data
directly over every characteristic-zero lift. -/
theorem cubic_section_of_zeroCycle_degree_one_of_coray_and_configurationCurveSteps
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    (curves : ∀ (K : Type u) [Field K] [CharZero K],
      ∀ (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3), p ≠ 0 →
        Smooth (hypersurfaceToBase p hp) →
        ∀ h : EffectiveZeroCycle (hypersurface p hp),
          EffectiveZeroCycle.degree (hypersurfaceToBase p hp) h = 3 →
          VoisinDegreeTenConfigurationCurveSteps
            (A := CoordinateRing (equationIdeal p hp)) (K := K)
            (grading (equationIdeal p hp))
            (show Proj (grading (equationIdeal p hp)) ⟶ Spec (.of K) from
              toBase (equationIdeal p hp)) h)
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ a : Spec (.of k) ⟶ hypersurface p hp,
      a ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  exact cubic_section_of_zeroCycle_degree_one_of_coray_and_degree_ten_family_geometry
    coray (fun K _ _ => voisinDegreeTenFamilyGeometryFor_of_configurationCurveSteps
      (curves K)) p hp z hz

/- The same all-characteristics assembly accepts collision-aware ordered
   relative-power curves directly.  This is a convenient split-cycle
   strengthening, not the narrowest boundary for Coray's degree-ten case:
   ordered `K`-valued endpoints do not in general represent a non-split
   degree-ten closed point.  The point-specific `RationalCycleFamily`
   interface remains the relevant geometric target there. -/
theorem cubic_section_of_zeroCycle_degree_one_of_coray_and_orderedTupleCurveSteps
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    (curves : ∀ (K : Type u) [Field K] [CharZero K],
      ∀ (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3), p ≠ 0 →
        Smooth (hypersurfaceToBase p hp) →
        ∀ h : EffectiveZeroCycle (hypersurface p hp),
          EffectiveZeroCycle.degree (hypersurfaceToBase p hp) h = 3 →
          VoisinDegreeTenOrderedTupleCurveSteps
            (K := K)
            (grading (equationIdeal p hp))
            (show Proj (grading (equationIdeal p hp)) ⟶ Spec (.of K) from
              toBase (equationIdeal p hp)) h)
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ a : Spec (.of k) ⟶ hypersurface p hp,
      a ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  exact cubic_section_of_zeroCycle_degree_one_of_coray_and_degree_ten_family_geometry
    coray (fun K _ _ => voisinDegreeTenFamilyGeometryFor_of_orderedTupleCurveSteps
      (curves K)) p hp z hz

/- The same ordered-power interface has a coordinate-level conclusion, making
   it directly consumable by the all-characteristics coordinate theorem. -/
theorem cubic_coordinates_of_zeroCycle_degree_one_of_coray_and_orderedTupleCurveSteps
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    (curves : ∀ (K : Type u) [Field K] [CharZero K],
      ∀ (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3), p ≠ 0 →
        Smooth (hypersurfaceToBase p hp) →
        ∀ h : EffectiveZeroCycle (hypersurface p hp),
          EffectiveZeroCycle.degree (hypersurfaceToBase p hp) h = 3 →
          VoisinDegreeTenOrderedTupleCurveSteps
            (K := K)
            (grading (equationIdeal p hp))
            (show Proj (grading (equationIdeal p hp)) ⟶ Spec (.of K) from
              toBase (equationIdeal p hp)) h)
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0 := by
  obtain ⟨a, ha⟩ :=
    cubic_section_of_zeroCycle_degree_one_of_coray_and_orderedTupleCurveSteps
      coray curves p hp z hz
  exact hypersurface_coordinates_of_point (RingHom.id k) p hp a (by simpa using ha)

end HomogeneousProjective
end AllCharacteristics
