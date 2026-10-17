import PfaffianDescent.CorayNativeSurfaceJetCoordinateSpanRank
import PfaffianDescent.CorayNativeLocalizedProjectiveHyperplanePullback

/-! Literal native localization coordinates identify the proved target
minor with unit normalization of the SAME fulljet vector. All tangent
nilpotent terms are retained, giving actual fulljet span rank three. -/
noncomputable section
namespace PfaffianDescent.Coray
open Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
universe u
set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Pulling the actual native projection coordinate through the actual
fulljet localization gives multiplication by the WHOLE unit inverse. -/
theorem nativeProjection_fulljet_coordinate_unitNormalization001
    {K R M : Type u} [CommRing K] [CommRing R] [Field M]
    {m : ℕ} (f : K →+* R) (x : Fin m → R) (a : Fin m)
    (J : R →+* SurfacePlaneJet M) (hUnit : IsUnit (J (x a)))
    (v : (SurfacePlaneJet M)ˣ) (hv : (↑v : SurfacePlaneJet M) = J (x a)) :
    let mu : Localization.Away (x a) →+* SurfacePlaneJet M := IsLocalization.Away.lift (x a) hUnit
    ∀ t : Fin m,
      mu (nativeLocalizedProjectiveChartMap f x a
        (chartCoordinate (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin m) K)) a t)) =
        J (x t) * (↑(v⁻¹) : SurfacePlaneJet M) := by
  let mu : Localization.Away (x a) →+* SurfacePlaneJet M := IsLocalization.Away.lift (x a) hUnit
  have hLift (r : R) : mu (algebraMap R (Localization.Away (x a)) r) = J r :=
    IsLocalization.Away.lift_eq (x a) hUnit r
  have hProduct : (↑v : SurfacePlaneJet M) * mu (IsLocalization.Away.invSelf (x a)) = 1 := by
    have h := congrArg mu (IsLocalization.Away.mul_invSelf (x a))
    rw [map_mul, map_one, hLift, ← hv] at h
    exact h
  have hInverse : mu (IsLocalization.Away.invSelf (x a)) = (↑(v⁻¹) : SurfacePlaneJet M) :=
    (Units.mul_eq_one_iff_inv_eq.mp hProduct).symm
  change ∀ t : Fin m,
    mu (nativeLocalizedProjectiveChartMap f x a
      (chartCoordinate (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin m) K)) a t)) =
      J (x t) * (↑(v⁻¹) : SurfacePlaneJet M)
  intro t
  have hCoordinate := (nativeLocalizedProjectiveChartMap_hyperplane_pullback001 f x a).2.1 t
  rw [hCoordinate, map_mul, hLift, hInverse]

/-- The proved actual normalized target-coordinate minor yields rank
three of the fulljet span on the SAME source coordinate vector. The
unit is constructed from actual denominator invertibility. -/
theorem nativeProjection_fulljet_coordinateSpan_finrank_three001
    {K R M : Type u} [CommRing K] [CommRing R] [Field M]
    {m : ℕ} (f : K →+* R) (x : Fin m → R) (a i k : Fin m)
    (J : R →+* SurfacePlaneJet M) (hUnit : IsUnit (J (x a)))
    (hMinor :
      let mu : Localization.Away (x a) →+* SurfacePlaneJet M := IsLocalization.Away.lift (x a) hUnit
      let row : Fin m → Fin 2 → M := fun t =>
        (mu (nativeLocalizedProjectiveChartMap f x a
          (chartCoordinate (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin m) K)) a t))).snd
      row i 0 * row k 1 - row i 1 * row k 0 ≠ 0) :
    finrank M (nativeSurfaceJetCoordinateSpan (fun t => J (x t))) = 3 := by
  classical
  have hUnitCopy := hUnit
  obtain ⟨v, hv⟩ := hUnitCopy
  have hCoordinate := nativeProjection_fulljet_coordinate_unitNormalization001 f x a J hUnit v hv
  have hMinor' :
      (J (x i) * (↑(v⁻¹) : SurfacePlaneJet M)).snd 0 *
        (J (x k) * (↑(v⁻¹) : SurfacePlaneJet M)).snd 1 -
      (J (x k) * (↑(v⁻¹) : SurfacePlaneJet M)).snd 0 *
        (J (x i) * (↑(v⁻¹) : SurfacePlaneJet M)).snd 1 ≠ 0 := by
    simpa only [hCoordinate, mul_comm] using hMinor
  exact nativeSurfaceJetCoordinateSpan_finrank_three_of_normalizedMinor001
    (fun t => J (x t)) a i k v hv.symm hMinor'

end PfaffianDescent.Coray
