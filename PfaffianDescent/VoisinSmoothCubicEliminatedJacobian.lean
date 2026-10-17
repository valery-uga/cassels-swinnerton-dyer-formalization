import PfaffianDescent.VoisinSmoothCubicEliminatedChart
import PfaffianDescent.VoisinFiniteVariableJacobianConverse

/-!
# Jacobian ideal of the dehomogenized smooth cubic

The actual normalized chart is a formally smooth principal quotient of
the polynomial ring in the three remaining variables. The finite-variable
converse Jacobian criterion therefore makes its three partial derivatives
generate the unit ideal. The comparison with the original four partials is
kept as a separate derivative-transport statement.
-/

namespace PfaffianDescent

open AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Smoothness of the actual cubic forces the derivatives of its
dehomogenized equation to generate the unit ideal on every affine chart. -/
theorem smoothCubic_eliminatedChart_jacobian_top
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0) [Smooth (hypersurfaceToBase p hp)] (j : Fin 4) :
    let I := equationIdeal p hp
    letI : Algebra K (ChartRing I j) := (chartBaseMap I j).toAlgebra
    let e : MvPolynomial {i : Fin 4 // i ≠ j} K →ₐ[K] ChartRing I j :=
      MvPolynomial.aeval (fun i => chartCoordinate I j i.1)
    Ideal.span (Set.range (fun i : {i : Fin 4 // i ≠ j} =>
      e (pderiv i (coordinateOneEvaluation j p)))) = ⊤ := by
  classical
  let I := equationIdeal p hp
  letI : Algebra K (ChartRing I j) := (chartBaseMap I j).toAlgebra
  let e : MvPolynomial {i : Fin 4 // i ≠ j} K →ₐ[K] ChartRing I j :=
    MvPolynomial.aeval (fun i => chartCoordinate I j i.1)
  obtain ⟨he, hker, hF⟩ :=
    smoothCubic_eliminatedChartMap_surjective_and_kernel p hp hp0 j
  letI : Algebra.FormallySmooth K (ChartRing I j) :=
    smoothCubic_chartAlgebra_formallySmooth p hp j
  exact formallySmooth_finitePrincipalPresentation_jacobian_top
    e he (coordinateOneEvaluation j p) hF hker

end PfaffianDescent
