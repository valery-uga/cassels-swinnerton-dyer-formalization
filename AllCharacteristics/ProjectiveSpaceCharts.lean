import AllCharacteristics.PolynomialCoordinateOne
import AllCharacteristics.AffineChartPresentation
import AllCharacteristics.RegularAffineStalks
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Polynomial charts and regularity of projective coefficient space

Each coordinate chart of the actual Proj of the zero homogeneous ideal is a
polynomial ring on the other coordinates. This identification preserves base
coefficients and proves smoothness of projective space and regularity of its
local stalks over a regular ring.
-/

open AlgebraicGeometry CategoryTheory MvPolynomial
namespace AllCharacteristics
namespace HomogeneousProjective
universe u
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "I₀" => (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R))

/-- A chart of projective space has just the relation X_j = 1. -/
theorem chartPresentationIdeal_bot (j : σ) :
    chartPresentationIdeal I₀ j = coordinateOneIdeal j := by
  simp [chartPresentationIdeal, coordinateOneIdeal]

/-- A polynomial algebra on the remaining coordinates is the actual affine
coordinate-chart ring of projective space. -/
noncomputable def chartPolynomialEquiv (j : σ) :
    MvPolynomial {i : σ // i ≠ j} R ≃+* ChartRing I₀ j :=
  (coordinateOneQuotientEquiv j).symm.toRingEquiv |>.trans
    ((Ideal.quotEquivOfEq (chartPresentationIdeal_bot (R := R) j).symm).trans
      (chartPresentationEquiv I₀ j))

/-- The polynomial presentation of a projective-space chart preserves constants. -/
theorem chartPolynomialEquiv_C (j : σ) (r : R) :
    chartPolynomialEquiv j (C r) = chartBaseMap I₀ j r := by
  have hc : (coordinateOneQuotientEquiv (R := R) j).symm (C r) =
      Ideal.Quotient.mk (coordinateOneIdeal j) (C r) :=
    (coordinateOneQuotientEquiv (R := R) j).symm.commutes r
  change chartPresentationEquiv I₀ j
    (Ideal.quotEquivOfEq (chartPresentationIdeal_bot (R := R) j).symm
      ((coordinateOneQuotientEquiv j).symm (C r))) = chartBaseMap I₀ j r
  rw [hc, Ideal.quotEquivOfEq_mk, chartPresentationEquiv_mk]
  exact MvPolynomial.eval₂_C _ _ r

/-- Projective-space chart rings are noetherian over a noetherian base. -/
instance isNoetherianRing_chartRing_bot [IsNoetherianRing R] [Finite σ] (j : σ) :
    IsNoetherianRing (ChartRing I₀ j) :=
  isNoetherianRing_of_ringEquiv (MvPolynomial {i : σ // i ≠ j} R) (chartPolynomialEquiv j)

/-- Projective-space chart rings are regular over a regular base. -/
instance isRegularRing_chartRing_bot [IsRegularRing R] [Finite σ] (j : σ) :
    IsRegularRing (ChartRing I₀ j) :=
  IsRegularRing.of_ringEquiv (chartPolynomialEquiv j)

/-- Each polynomial chart has a smooth coefficient homomorphism. -/
theorem smooth_chartBaseMap_bot [Finite σ] (j : σ) : (chartBaseMap I₀ j).Smooth := by
  let := (chartBaseMap I₀ j).toAlgebra
  change Algebra.Smooth R (ChartRing I₀ j)
  let e : MvPolynomial {i : σ // i ≠ j} R ≃ₐ[R] ChartRing I₀ j :=
    { chartPolynomialEquiv j with commutes' := chartPolynomialEquiv_C j }
  have : Algebra.Smooth R (MvPolynomial {i : σ // i ≠ j} R) :=
    { formallySmooth := inferInstance, finitePresentation := inferInstance }
  exact Algebra.Smooth.of_equiv e

/-- The actual projective space is smooth over its coefficient ring. -/
theorem smooth_toBase_bot [Finite σ] : Smooth (toBase I₀) := by
  have : IsZariskiLocalAtSource (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)
  apply (IsZariskiLocalAtSource.iff_of_openCover (P := @Smooth.{u})
    (coordinateOpenCover I₀).openCover).mpr
  intro j
  change σ at j
  change Smooth (chartι I₀ j ≫ toBase I₀)
  rw [chartι_toBase]
  exact (HasRingHomProperty.Spec_iff (P := @Smooth.{u})).mpr (smooth_chartBaseMap_bot j)

/-- Every stalk of projective space over a regular ring is a regular local ring. -/
theorem isRegularLocalRing_projectiveSpace_stalk [IsRegularRing R] [Finite σ]
    (x : scheme I₀) : IsRegularLocalRing ((scheme I₀).presheaf.stalk x) := by
  obtain ⟨j, y, hy⟩ := exists_coordinate_chart I₀ x
  have := isRegularLocalRing_spec_stalk (ChartRing I₀ j) y
  have hr : IsRegularLocalRing ((scheme I₀).presheaf.stalk (chartι I₀ j y)) :=
    IsRegularLocalRing.of_ringEquiv
      (asIso ((chartι I₀ j).stalkMap y)).commRingCatIsoToRingEquiv.symm
  exact hy ▸ hr

end HomogeneousProjective
end AllCharacteristics
