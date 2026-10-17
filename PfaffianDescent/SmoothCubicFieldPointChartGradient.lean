import PfaffianDescent.VoisinCoordinateOnePDeriv
import AllCharacteristics.ProjectivePointCoordinates

/-! Smoothness forces a nonzero retained partial at the actual chosen chart
of any original field point. The differential certificate is derived by
specializing the checked actual chart Jacobian unit ideal. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem smoothCubic_fieldPoint_chart_exists_nonzero_retained_partial
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (j : Fin 4) (g : ChartRing (equationIdeal p hp) j →+* L)
    (hbase : g.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K L) :
    ∃ a : {a : Fin 4 // a ≠ j},
      (pderiv a.1 p).eval₂ (algebraMap K L)
        (fun b => g (chartCoordinate (equationIdeal p hp) j b)) ≠ 0 := by
  classical
  let I := equationIdeal p hp
  letI : Algebra K (ChartRing I j) := (chartBaseMap I j).toAlgebra
  let e : MvPolynomial {a : Fin 4 // a ≠ j} K →ₐ[K] ChartRing I j :=
    aeval (fun a => chartCoordinate I j a.1)
  have hjac : Ideal.span (Set.range (fun a : {a : Fin 4 // a ≠ j} =>
      e (pderiv a (coordinateOneEvaluation j p)))) = ⊤ :=
    smoothCubic_eliminatedChart_jacobian_top p hp hp0 j
  by_contra h
  push Not at h
  have hall : ∀ a : {a : Fin 4 // a ≠ j},
      g (e (pderiv a (coordinateOneEvaluation j p))) = 0 := by
    intro a
    have heq := smoothCubic_eliminatedChart_pderiv_eq_original p hp j a
    change e (pderiv a (coordinateOneEvaluation j p)) =
      (pderiv a.1 p).eval₂ (chartBaseMap I j) (chartCoordinate I j) at heq
    rw [heq, hom_eval₂, hbase]
    exact h a
  have hle : Ideal.span (Set.range (fun a : {a : Fin 4 // a ≠ j} =>
      e (pderiv a (coordinateOneEvaluation j p)))) ≤ RingHom.ker g := by
    apply Ideal.span_le.mpr
    rintro q ⟨a, rfl⟩
    exact hall a
  rw [hjac] at hle
  have hone := hle (show (1 : ChartRing I j) ∈ ⊤ from trivial)
  change g 1 = 0 at hone
  simpa using hone

end PfaffianDescent
