import PfaffianDescent.LinearNormalizedProjectivePoint
import AllCharacteristics.ProjectivePointCoordinates

/-! Comparing two normalized vectors that define the same projective point. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Two homogeneous coordinate vectors normalized by possibly different
linear forms differ by one nonzero scalar when they define the same
field-valued projective point. -/
theorem linearNormalizedPoint_vectors_proportional
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (x y : Fin 4 → F)
    (ellx elly : MvPolynomial (Fin 4) K)
    (hellx : ellx.IsHomogeneous 1) (helly : elly.IsHomogeneous 1)
    (hxell : ellx.eval₂ (algebraMap K F) x = 1)
    (hyell : elly.eval₂ (algebraMap K F) y = 1)
    (hex : ∀ p ∈ I.toIdeal, p.eval₂ (algebraMap K F) x = 0)
    (hey : ∀ p ∈ I.toIdeal, p.eval₂ (algebraMap K F) y = 0)
    (hpoint : linearNormalizedPoint I x ellx hellx hxell hex =
      linearNormalizedPoint I y elly helly hyell hey)
    (j : Fin 4) (hxj : x j ≠ 0) (hyj : y j ≠ 0) :
    ∀ i : Fin 4, y i = (y j / x j) * x i := by
  let ux : Fˣ := Units.mk0 (x j) hxj
  let uy : Fˣ := Units.mk0 (y j) hyj
  obtain ⟨gx, hgx, hpx⟩ :=
    exists_coordinateChartMap_eq_linearNormalizedPoint
      I x ellx hellx hxell hex j ux rfl
  obtain ⟨gy, hgy, hpy⟩ :=
    exists_coordinateChartMap_eq_linearNormalizedPoint
      I y elly helly hyell hey j uy rfl
  have hgeq : gx = gy :=
    chart_hom_eq_of_projective_eq I gx gy
      (hpx.trans (hpoint.trans hpy.symm))
  intro i
  have hratio : (x j)⁻¹ * x i = (y j)⁻¹ * y i := by
    have h := congrArg
      (fun g : ChartRing I j →+* F => g (chartCoordinate I j i)) hgeq
    rw [hgx i, hgy i] at h
    simpa [ux, uy] using h
  calc
    y i = y j * ((y j)⁻¹ * y i) := by simp [hyj]
    _ = y j * ((x j)⁻¹ * x i) := by rw [hratio]
    _ = (y j / x j) * x i := by rw [div_eq_mul_inv, mul_assoc]

end PfaffianDescent
