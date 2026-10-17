import PfaffianDescent.VoisinCoordinateOnePDeriv
import PfaffianDescent.CubicThreePointFirstJets

noncomputable section
open AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

def cubicClosedPointSerreSurfaceJets_vertex (i j : Fin 4) : K :=
  if i = j then 1 else 0

theorem cubicClosedPointSerreSurfaceJets_coordinateOne_vertex (i : Fin 4) :
    (aeval (fun _ : {j : Fin 4 // j ≠ i} => (0 : K))).comp
      (coordinateOneEvaluation (R := K) i) =
      aeval (cubicClosedPointSerreSurfaceJets_vertex (K := K) i) := by
  apply MvPolynomial.algHom_ext
  intro j
  by_cases h : j = i
  · subst j
    simp [coordinateOneEvaluation, cubicClosedPointSerreSurfaceJets_vertex]
  · simp [coordinateOneEvaluation, cubicClosedPointSerreSurfaceJets_vertex, h, Ne.symm h]

/-- Actual smoothness forces a nonzero retained partial at an actual
coordinate vertex on the cubic. The actual chart Jacobian unit ideal is
specialized through its principal polynomial presentation. -/
theorem cubicClosedPointSerreSurfaceJets_exists_nonzero_gradient
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (i : Fin 4)
    (hvertex : aeval (cubicClosedPointSerreSurfaceJets_vertex (K := K) i) p = 0) :
    ∃ j : Fin 4, j ≠ i ∧
      aeval (cubicClosedPointSerreSurfaceJets_vertex (K := K) i) (pderiv j p) ≠ 0 := by
  classical
  let I := equationIdeal p hp
  letI : Algebra K (ChartRing I i) := (chartBaseMap I i).toAlgebra
  let e : MvPolynomial {j : Fin 4 // j ≠ i} K →ₐ[K] ChartRing I i :=
    aeval (fun j => chartCoordinate I i j.1)
  let v : MvPolynomial {j : Fin 4 // j ≠ i} K →ₐ[K] K := aeval (fun _ => 0)
  obtain ⟨he, hker, _⟩ := smoothCubic_eliminatedChartMap_surjective_and_kernel p hp hp0 i
  have hcomp : v.comp (coordinateOneEvaluation (R := K) i) =
      aeval (cubicClosedPointSerreSurfaceJets_vertex (K := K) i) :=
    cubicClosedPointSerreSurfaceJets_coordinateOne_vertex (K := K) i
  have hv : v (coordinateOneEvaluation i p) = 0 := by
    rw [← AlgHom.comp_apply, hcomp]
    exact hvertex
  have hle : RingHom.ker e.toRingHom ≤ RingHom.ker v.toRingHom := by
    rw [hker]
    apply Ideal.span_le.mpr
    rintro f rfl
    exact hv
  let ψ : ChartRing I i →ₐ[K] K := AlgHom.liftOfSurjective e he v hle
  by_contra hn
  have hall : ∀ j : {j : Fin 4 // j ≠ i},
      ψ (e (pderiv j (coordinateOneEvaluation i p))) = 0 := by
    intro j
    rw [AlgHom.liftOfSurjective_apply]
    rw [pderiv_coordinateOneEvaluation, ← AlgHom.comp_apply, hcomp]
    by_contra hne
    exact hn ⟨j.1, j.2, hne⟩
  have hjac : Ideal.span (Set.range (fun j : {j : Fin 4 // j ≠ i} =>
      e (pderiv j (coordinateOneEvaluation i p)))) = ⊤ :=
    smoothCubic_eliminatedChart_jacobian_top p hp hp0 i
  have hcontained : Ideal.span (Set.range (fun j : {j : Fin 4 // j ≠ i} =>
      e (pderiv j (coordinateOneEvaluation i p)))) ≤ RingHom.ker ψ.toRingHom := by
    apply Ideal.span_le.mpr
    rintro f ⟨j, rfl⟩
    exact hall j
  rw [hjac] at hcontained
  have hone := hcontained (show (1 : ChartRing I i) ∈ ⊤ from trivial)
  change ψ 1 = 0 at hone
  simpa using hone

end PfaffianDescent
