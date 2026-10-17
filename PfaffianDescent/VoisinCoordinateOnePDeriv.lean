import AllCharacteristics.PolynomialCoordinateOne
import Mathlib.Algebra.MvPolynomial.PDeriv
import PfaffianDescent.VoisinSmoothCubicEliminatedChart
import PfaffianDescent.VoisinSmoothCubicEliminatedJacobian

/-!
# Partial derivatives after setting one projective coordinate to one

The derivative in any retained variable commutes with the explicit
coordinate-one evaluation map. This is the derivative transport needed to
apply the principal Jacobian converse to a dehomogenized cubic chart.
-/

namespace PfaffianDescent

open MvPolynomial
open AlgebraicGeometry
open AllCharacteristics.HomogeneousProjective

universe u

variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem pderiv_coordinateOneEvaluation
    (j : Fin 4) (i : {k : Fin 4 // k ≠ j})
    (p : MvPolynomial (Fin 4) K) :
    pderiv i (coordinateOneEvaluation j p) =
      coordinateOneEvaluation j (pderiv i.1 p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp [coordinateOneEvaluation]
  | add p q hp hq => simp [hp, hq]
  | mul_X p k hp =>
      rw [map_mul, pderiv_mul, hp, pderiv_mul, map_add, map_mul, map_mul]
      by_cases hkj : k = j
      · subst k
        simp [coordinateOneEvaluation, pderiv_X, i.property]
      · simpa [coordinateOneEvaluation, hkj, pderiv_X,
          Pi.single_apply, Subtype.ext_iff]

/-- Evaluation of a dehomogenized polynomial on the actual normalized chart
equals evaluation of the original polynomial there. -/
theorem smoothCubic_eliminatedChartMap_comp_coordinateOneEvaluation
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (j : Fin 4) :
    let I := equationIdeal p hp
    letI : Algebra K (ChartRing I j) := (chartBaseMap I j).toAlgebra
    let e : MvPolynomial {i : Fin 4 // i ≠ j} K →ₐ[K] ChartRing I j :=
      MvPolynomial.aeval (fun i => chartCoordinate I j i.1)
    e.comp (coordinateOneEvaluation j) =
      MvPolynomial.aeval (chartCoordinate I j) := by
  let I := equationIdeal p hp
  letI : Algebra K (ChartRing I j) := (chartBaseMap I j).toAlgebra
  let e : MvPolynomial {i : Fin 4 // i ≠ j} K →ₐ[K] ChartRing I j :=
    MvPolynomial.aeval (fun i => chartCoordinate I j i.1)
  apply MvPolynomial.algHom_ext
  intro i
  by_cases hi : i = j
  · subst i
    simp [e, coordinateOneEvaluation, chartCoordinate_self]
  · simp [e, coordinateOneEvaluation, hi]

/-- The partial derivative of the dehomogenized equation, evaluated on
the actual chart, is the corresponding projective partial derivative. -/
theorem smoothCubic_eliminatedChart_pderiv_eq_original
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (j : Fin 4) (i : {k : Fin 4 // k ≠ j}) :
    let I := equationIdeal p hp
    letI : Algebra K (ChartRing I j) := (chartBaseMap I j).toAlgebra
    let e : MvPolynomial {k : Fin 4 // k ≠ j} K →ₐ[K] ChartRing I j :=
      MvPolynomial.aeval (fun k => chartCoordinate I j k.1)
    e (pderiv i (coordinateOneEvaluation j p)) =
      (MvPolynomial.aeval (chartCoordinate I j)) (pderiv i.1 p) := by
  dsimp only
  rw [pderiv_coordinateOneEvaluation]
  have h := smoothCubic_eliminatedChartMap_comp_coordinateOneEvaluation
    p hp j
  have hi := DFunLike.congr_fun h (pderiv i.1 p)
  simpa only [AlgHom.comp_apply] using hi

/-- Smoothness of the cubic alone gives the four-partial Jacobian unit ideal
on every actual normalized chart. The three retained partials already
generate the unit ideal. -/
theorem smoothCubic_chartJacobian_top
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0) [Smooth (hypersurfaceToBase p hp)] (j : Fin 4) :
    let I := equationIdeal p hp
    Ideal.span (Set.range (fun i : Fin 4 =>
      (pderiv i p).eval₂ (chartBaseMap I j) (chartCoordinate I j))) = ⊤ := by
  let I := equationIdeal p hp
  letI : Algebra K (ChartRing I j) := (chartBaseMap I j).toAlgebra
  let e : MvPolynomial {i : Fin 4 // i ≠ j} K →ₐ[K] ChartRing I j :=
    MvPolynomial.aeval (fun i => chartCoordinate I j i.1)
  let f : MvPolynomial (Fin 4) K →ₐ[K] ChartRing I j :=
    MvPolynomial.aeval (chartCoordinate I j)
  have hthree : Ideal.span (Set.range (fun i : {k : Fin 4 // k ≠ j} =>
      e (pderiv i (coordinateOneEvaluation j p)))) = ⊤ :=
    smoothCubic_eliminatedChart_jacobian_top p hp hp0 j
  have hle : Ideal.span (Set.range (fun i : {k : Fin 4 // k ≠ j} =>
      e (pderiv i (coordinateOneEvaluation j p)))) ≤
      Ideal.span (Set.range (fun i : Fin 4 => f (pderiv i p))) := by
    apply Ideal.span_le.mpr
    intro a ha
    obtain ⟨i, rfl⟩ := ha
    have hi := smoothCubic_eliminatedChart_pderiv_eq_original p hp j i
    change e (pderiv i (coordinateOneEvaluation j p)) =
      f (pderiv i.1 p) at hi
    change e (pderiv i (coordinateOneEvaluation j p)) ∈
      Ideal.span (Set.range (fun i : Fin 4 => f (pderiv i p)))
    rw [hi]
    exact Ideal.subset_span ⟨i.1, rfl⟩
  have hfour : Ideal.span (Set.range (fun i : Fin 4 =>
      f (pderiv i p))) = ⊤ := top_unique (hthree ▸ hle)
  change Ideal.span (Set.range (fun i : Fin 4 =>
    (pderiv i p).eval₂ (chartBaseMap I j) (chartCoordinate I j))) = ⊤ at hfour
  simpa only [I] using hfour

end PfaffianDescent
