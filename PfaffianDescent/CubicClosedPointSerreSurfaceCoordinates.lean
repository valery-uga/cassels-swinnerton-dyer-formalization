import PfaffianDescent.CubicClosedPointSerreSurfaceCoordinatesChange

/-! # Native surface coordinate normalization from actual cone points -/
noncomputable section
open AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The literal column matrix takes each standard vertex to its original
chosen cone point. -/
theorem cubicClosedPointSerreSurfaceCoordinates_mulVec_vertex
    (x : Fin 4 → Fin 4 → K) (i : Fin 4) :
    (Matrix.of (fun r j => x j r)).mulVec
      (cubicClosedPointSerreSurfaceJets_vertex (K := K) i) = x i := by
  classical
  funext r
  simp [Matrix.mulVec, dotProduct, cubicClosedPointSerreSurfaceJets_vertex]

/-- An actual smooth cubic admits a literal invertible coordinate change
whose transformed equation contains all four standard vertices. The original
nonzero cone points, matrix, inverse normalization, smoothness, and primeness
are constructed from the original cubic. -/
theorem cubicClosedPointSerreSurfaceCoordinates_exists_native
    [IsAlgClosed K] (p : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    ∃ x : Fin 4 → cubicSurfaceAffinePoints p,
    ∃ hM : IsUnit (Matrix.of (fun r j => (x j).1 r)).det,
      let M := Matrix.of (fun r j => (x j).1 r)
      (∀ i, M.mulVec (cubicClosedPointSerreSurfaceJets_vertex (K := K) i) = (x i).1) ∧
      (∀ i, M⁻¹.mulVec (x i).1 = cubicClosedPointSerreSurfaceJets_vertex (K := K) i) ∧
      LinearIndependent K (fun i => (x i).1) ∧
      (linearSubstitution M p).IsHomogeneous 3 ∧
      linearSubstitution M p ≠ 0 ∧
      Smooth (hypersurfaceToBase (linearSubstitution M p)
        (linearSubstitution_homogeneous M hp)) ∧
      (Ideal.span ({linearSubstitution M p} : Set (MvPolynomial (Fin 4) K))).IsPrime ∧
      ∀ i : Fin 4,
        aeval (cubicClosedPointSerreSurfaceJets_vertex (K := K) i)
          (linearSubstitution M p) = 0 := by
  obtain ⟨x, hM⟩ := cubicClosedPointSerreSurfaceCoordinates_exists_basis p hp hp0
  let M := Matrix.of (fun r j => (x j).1 r)
  have hv (i : Fin 4) : M.mulVec
      (cubicClosedPointSerreSurfaceJets_vertex (K := K) i) = (x i).1 :=
    cubicClosedPointSerreSurfaceCoordinates_mulVec_vertex (fun j => (x j).1) i
  have hinv (i : Fin 4) : M⁻¹.mulVec (x i).1 =
      cubicClosedPointSerreSurfaceJets_vertex (K := K) i := by
    rw [← hv i, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hM, Matrix.one_mulVec]
  have hli : LinearIndependent K (fun i => (x i).1) := by
    change LinearIndependent K M.col
    exact Matrix.linearIndependent_cols_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det M).mpr hM)
  have hp' := linearSubstitution_homogeneous M hp
  have hp0' := cubicClosedPointSerreSurfaceCoordinates_nonzero M hM p hp0
  letI : Smooth (hypersurfaceToBase (linearSubstitution M p) hp') :=
    cubicClosedPointSerreSurfaceCoordinates_smooth M hM p hp
  refine ⟨x, hM, hv, hinv, hli, hp', hp0', inferInstance, ?_, ?_⟩
  · exact principalIdeal_prime_of_smooth_homogeneous_cubic (linearSubstitution M p) hp' hp0'
  · intro i
    rw [linearSubstitution_eval, hv i]
    exact (x i).2.1

end PfaffianDescent
