import AllCharacteristics.AmbientChartPresentation
import AllCharacteristics.AffineChartPresentation

/-!
# The local equation ideal of a projective hypersurface

The ambient coordinate chart is a polynomial quotient by `X_j - 1`.
The hypersurface chart is the further quotient by its homogeneous equation.
The resulting chart map therefore has the normalized equation as its kernel.
-/

open MvPolynomial HomogeneousLocalization
namespace AllCharacteristics
namespace HomogeneousProjective

universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "𝒜" => MvPolynomial.homogeneousSubmodule σ R

/-- Restriction from an ambient chart to a hypersurface chart preserves base
coefficients. -/
theorem hypersurfaceAmbientChartMap_baseMap
    (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d)
    (j : σ) (r : R) :
    hypersurfaceAmbientChartMap p hp j
      (GradedChart.baseMap 𝒜 (z := MvPolynomial.X j) r) =
      chartBaseMap (equationIdeal p hp) j r := by
  rfl

/-- Polynomial evaluation on the hypersurface chart factors through
evaluation on the ambient chart. -/
theorem hypersurfaceAmbientChartMap_comp_ambientChartEvaluation
    (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d) (j : σ) :
    (hypersurfaceAmbientChartMap p hp j).comp (ambientChartEvaluation j) =
      MvPolynomial.eval₂Hom (chartBaseMap (equationIdeal p hp) j)
        (chartCoordinate (equationIdeal p hp) j) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simpa only [RingHom.comp_apply, ambientChartEvaluation, MvPolynomial.eval₂Hom_C]
      using hypersurfaceAmbientChartMap_baseMap p hp j r
  · intro i
    simpa only [RingHom.comp_apply, ambientChartEvaluation, MvPolynomial.eval₂Hom_X',
      ambientChartCoordinate]
      using hypersurfaceAmbientChartMap_coordinate p hp j i

/-- The affine hypersurface chart-map kernel is the image of the polynomial
chart-presentation ideal under ambient normalized evaluation. -/
theorem hypersurfaceAmbientChartMap_ker_eq_presentationImage
    (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d) (j : σ) :
    RingHom.ker (hypersurfaceAmbientChartMap p hp j) =
      (chartPresentationIdeal (equationIdeal p hp) j).map
        (ambientChartEvaluation j) := by
  let f := hypersurfaceAmbientChartMap p hp j
  let evA := ambientChartEvaluation (R := R) (σ := σ) j
  let evB := MvPolynomial.eval₂Hom (chartBaseMap (equationIdeal p hp) j)
    (chartCoordinate (equationIdeal p hp) j)
  have hcomp : f.comp evA = evB :=
    hypersurfaceAmbientChartMap_comp_ambientChartEvaluation p hp j
  have hkerB : RingHom.ker evB = chartPresentationIdeal (equationIdeal p hp) j :=
    chartEvaluation_ker (equationIdeal p hp) j
  apply le_antisymm
  · intro x hx
    obtain ⟨P, rfl⟩ := ambientChartEvaluation_surjective (R := R) (σ := σ) j x
    apply Ideal.mem_map_of_mem evA
    rw [← hkerB]
    change evB P = 0
    rw [← hcomp]
    exact hx
  · rw [Ideal.map_le_iff_le_comap]
    intro P hP
    change f (evA P) = 0
    rw [← RingHom.comp_apply, hcomp]
    have hPB : P ∈ RingHom.ker evB := by simpa only [hkerB] using hP
    exact hPB

/-- The normalized homogeneous equation generates the entire kernel of the
ambient-to-hypersurface affine chart ring map. -/
theorem hypersurfaceAmbientChartMap_ker_eq_equation
    (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d) (j : σ) :
    RingHom.ker (hypersurfaceAmbientChartMap p hp j) =
      Ideal.span ({Away.mk 𝒜 (MvPolynomial.isHomogeneous_X R j) d p
        (by simpa using hp)} : Set (Away 𝒜 (MvPolynomial.X j))) := by
  let evA := ambientChartEvaluation (R := R) (σ := σ) j
  have hA : (ambientChartPresentationIdeal (R := R) (σ := σ) j).map evA = ⊥ := by
    apply (Ideal.map_eq_bot_iff_le_ker evA).mpr
    rw [ambientChartEvaluation_ker]
  rw [hypersurfaceAmbientChartMap_ker_eq_presentationImage]
  change (Ideal.span ({p} : Set (MvPolynomial σ R)) ⊔
    ambientChartPresentationIdeal j).map evA = _
  rw [Ideal.map_sup, hA, sup_bot_eq, Ideal.map_span, Set.image_singleton]
  exact congrArg (fun x : Away 𝒜 (MvPolynomial.X j) => Ideal.span ({x} : Set _))
    (ambientChartEvaluation_homogeneous j p hp)

end HomogeneousProjective
end AllCharacteristics
