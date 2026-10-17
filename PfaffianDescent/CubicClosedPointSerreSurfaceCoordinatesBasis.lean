import PfaffianDescent.CubicSurfacePointEvaluation
import PfaffianDescent.CubicFiniteSubschemeHyperplane
import PfaffianDescent.PolynomialLinearChange
import PfaffianDescent.CubicClosedPointSerreSurfaceJetsGradient

noncomputable section
open AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- Evaluating a literal linear form at a coordinate vertex extracts its
corresponding coefficient. -/
theorem cubicClosedPointSerreSurfaceCoordinates_linearForm_vertex
    (c : Fin 4 → K) (i : Fin 4) :
    aeval (cubicClosedPointSerreSurfaceJets_vertex (K := K) i)
      (homogeneousLinearForm c) = c i := by
  classical
  rw [homogeneousLinearForm_eval]
  simp [cubicClosedPointSerreSurfaceJets_vertex]

/-- Four actual nonzero cone points on a smooth cubic form an actual
invertible coordinate matrix. Primeness, linear-section separation, and the
four-dimensional section space are proved from the cubic. -/
theorem cubicClosedPointSerreSurfaceCoordinates_exists_basis
    [IsAlgClosed K] (p : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    ∃ x : Fin 4 → cubicSurfaceAffinePoints p,
      IsUnit (Matrix.of (fun i j => (x j).1 i)).det := by
  classical
  let W := homogeneousSubmodule (Fin 4) K 1
  letI : FiniteDimensional K W := Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg _ _ _)
  have hprime := principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0
  obtain ⟨s, hscard, hbij⟩ := exists_cubicSurfaceAffinePoint_finset_evaluation_bijective
    p (d := 1) (by decide) hprime W (fun _ hq => hq) (by
      intro q hq hqmem
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hqmem
      have hrp : r * p = q := by rw [mul_comm]; exact hr.symm
      have hrzero : r = 0 := eq_zero_of_mul_homogeneous_lt hp hp0 (by
        rw [hrp]; exact hq) (by decide)
      rw [← hrp, hrzero, zero_mul])
  have hs4 : s.card = 4 := by
    rw [four_variable_homogeneous_finrank] at hscard
    norm_num at hscard
    exact hscard
  let e : Fin 4 ≃ s := (Fintype.equivFinOfCardEq (α := s) (by simpa using hs4)).symm
  let x : Fin 4 → cubicSurfaceAffinePoints p := fun i => (e i).1
  let T : Matrix (Fin 4) (Fin 4) K := fun i j => (x i).1 j
  have hT : IsUnit T := Matrix.mulVec_injective_iff_isUnit.mp (by
    intro c d hcd
    let qc : W := ⟨homogeneousLinearForm c, homogeneousLinearForm_isHomogeneous c⟩
    let qd : W := ⟨homogeneousLinearForm d, homogeneousLinearForm_isHomogeneous d⟩
    have heval : (finsetEvaluation s).comp (cubicSurfacePointEvaluation p W) qc =
        (finsetEvaluation s).comp (cubicSurfacePointEvaluation p W) qd := by
      funext z
      obtain ⟨i, rfl⟩ := e.surjective z
      have hi := congrFun hcd i
      change aeval (x i).1 (homogeneousLinearForm c) =
        aeval (x i).1 (homogeneousLinearForm d)
      rw [homogeneousLinearForm_eval, homogeneousLinearForm_eval]
      simpa only [T, Matrix.mulVec, dotProduct, mul_comm] using hi
    have hq : homogeneousLinearForm c = homogeneousLinearForm d :=
      congrArg Subtype.val (hbij.1 heval)
    funext i
    have hi := congrArg (aeval (cubicClosedPointSerreSurfaceJets_vertex (K := K) i)) hq
    simpa only [cubicClosedPointSerreSurfaceCoordinates_linearForm_vertex] using hi)
  refine ⟨x, ?_⟩
  have hdet := (Matrix.isUnit_iff_isUnit_det T).mp hT
  change IsUnit T.transpose.det
  rw [Matrix.det_transpose]
  exact hdet

end PfaffianDescent
