import AllCharacteristics.ProjectiveChartOverlap
import AllCharacteristics.HomogeneousSpecialization
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Tactic.Ring

/-! SOURCE ONLY175. Cubic homogeneity and actual projective chart maps
produce the derivative transition. Unit differentiation cancels precisely
this factor, without dividing by the degree or any characteristic premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u

/-- The native differential of an inverse coordinate cancels the actual
quadratic partial-derivative transition factor. -/
theorem nativeUnitDifferential_quadraticTransition_cancel175
    {K R : Type u} [CommRing K] [CommRing R] [Algebra K R]
    (u a : Rˣ) :
    (((u ^ 2 * a)⁻¹ : Rˣ) : R) • KaehlerDifferential.D K R (u : R) =
      -(((a⁻¹ : Rˣ) : R) • KaehlerDifferential.D K R ((u⁻¹ : Rˣ) : R)) := by
  have hd := (KaehlerDifferential.D K R).leibniz_of_mul_eq_one
    (show (u : R) * ((u⁻¹ : Rˣ) : R) = 1 by simp)
  have hc : (((u ^ 2 * a)⁻¹ : Rˣ) : R) * (u : R) ^ 2 = ((a⁻¹ : Rˣ) : R) := by
    change (((u ^ 2 * a)⁻¹ * u ^ 2 : Rˣ) : R) = ((a⁻¹ : Rˣ) : R)
    congr 1
    simp [mul_inv_rev]
  rw [hd, neg_smul, smul_neg, smul_smul, hc]

section ActualOverlap
variable {K : Type u} [CommRing K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- On the SAME actual projective intersection, the chosen derivative of a
cubic scales by the square of the original coordinate transition unit. -/
theorem planeCubic_actualProjectiveOverlap_partial_transition175
    (p : MvPolynomial (Fin 3) K) (hp : p.IsHomogeneous 3) (j l m : Fin 3) :
    let I := equationIdeal p hp
    chartOverlapRightMap I j l
      ((pderiv m p).eval₂ (chartBaseMap I l) (chartCoordinate I l)) =
      (chartOverlapUnit I j l : ChartOverlapRing I j l) ^ 2 *
        chartOverlapLeftMap I j l
          ((pderiv m p).eval₂ (chartBaseMap I j) (chartCoordinate I j)) := by
  let I := equationIdeal p hp
  let H := ChartOverlapRing I j l
  let b : K →+* H := GradedChart.baseMap (grading I)
    (z := coordinate I j * coordinate I l)
  have hleft : (chartOverlapLeftMap I j l).comp (chartBaseMap I j) = b := by
    apply RingHom.ext
    intro c
    exact chartOverlapLeftMap_baseMap I j l c
  have hright : (chartOverlapRightMap I j l).comp (chartBaseMap I l) = b := by
    apply RingHom.ext
    intro c
    exact chartOverlapRightMap_baseMap I j l c
  have hx : (fun n => chartOverlapRightMap I j l (chartCoordinate I l n)) =
      (chartOverlapUnit I j l : H) •
        (fun n => chartOverlapLeftMap I j l (chartCoordinate I j n)) := by
    funext n
    change chartOverlapRightMap I j l (chartCoordinate I l n) =
      (chartOverlapUnit I j l : H) * chartOverlapLeftMap I j l (chartCoordinate I j n)
    rw [chartOverlap_coordinate_relation]
    simp [← mul_assoc]
  change chartOverlapRightMap I j l
    ((pderiv m p).eval₂ (chartBaseMap I l) (chartCoordinate I l)) =
    (chartOverlapUnit I j l : H) ^ 2 *
      chartOverlapLeftMap I j l
        ((pderiv m p).eval₂ (chartBaseMap I j) (chartCoordinate I j))
  rw [MvPolynomial.hom_eval₂, MvPolynomial.hom_eval₂, hleft, hright, hx]
  exact eval₂_homogeneous_smul (pderiv m p) (by simpa using hp.pderiv)
    b _ (chartOverlapUnit I j l : H)

end ActualOverlap
end PfaffianDescent.Coray
