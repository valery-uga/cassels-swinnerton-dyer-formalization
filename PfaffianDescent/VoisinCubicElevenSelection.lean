import PfaffianDescent.CubicSurfacePointEvaluation
import PfaffianDescent.VoisinSectionLinearAlgebra

/-!
# Eleven-point evaluation selected for a fixed cubic section system

The existing maximal-rank theorem supplies eleven geometric points for
each fixed finite-dimensional subsystem. Selecting those points once lets
the numerical kernel calculation be checked in a separate declaration.
-/

namespace PfaffianDescent

open AlgebraicGeometry MvPolynomial Module
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable def cubicElevenMaximalRankPoints
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (W : Submodule K (grading (equationIdeal p hp) 3))
    [FiniteDimensional K W] : Finset (cubicSurfaceAffinePoints p) :=
  Classical.choose
    (exists_eleven_cubicSurfaceCoordinateSubmodule_maximalRank_evaluation
      p hp hp0 hprime (d := 3) (by decide) W)

theorem cubicElevenMaximalRankPoints_card
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (W : Submodule K (grading (equationIdeal p hp) 3))
    [FiniteDimensional K W] :
    (cubicElevenMaximalRankPoints p hp hp0 hprime W).card = 11 :=
  (Classical.choose_spec
    (exists_eleven_cubicSurfaceCoordinateSubmodule_maximalRank_evaluation
      p hp hp0 hprime (d := 3) (by decide) W)).1

noncomputable def cubicElevenSelectedEvaluation
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (W : Submodule K (grading (equationIdeal p hp) 3))
    [FiniteDimensional K W] :
    W →ₗ[K] (cubicElevenMaximalRankPoints p hp hp0 hprime W → K) :=
  (finsetEvaluation (cubicElevenMaximalRankPoints p hp hp0 hprime W)).comp
    ((cubicSurfaceCoordinatePointEvaluation p hp (d := 3)).domRestrict W)

set_option backward.isDefEq.respectTransparency false in
theorem cubicElevenSelectedEvaluation_maximalRank
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (W : Submodule K (grading (equationIdeal p hp) 3))
    [FiniteDimensional K W] :
    Function.Surjective (cubicElevenSelectedEvaluation p hp hp0 hprime W) ∨
      Function.Injective (cubicElevenSelectedEvaluation p hp hp0 hprime W) := by
  exact (Classical.choose_spec
    (exists_eleven_cubicSurfaceCoordinateSubmodule_maximalRank_evaluation
      p hp hp0 hprime (d := 3) (by decide) W)).2.1

set_option backward.isDefEq.respectTransparency false in
theorem cubicElevenMaximalRankPoints_target_finrank
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (W : Submodule K (grading (equationIdeal p hp) 3))
    [FiniteDimensional K W] :
    finrank K (cubicElevenMaximalRankPoints p hp hp0 hprime W → K) = 11 := by
  rw [Module.finrank_pi_fintype]
  simpa using cubicElevenMaximalRankPoints_card p hp hp0 hprime W

/-- For a cubic section subsystem of dimension at most twelve, evaluation at
the selected eleven geometric points leaves a kernel of dimension at most
one.  This is the exact fixed-conic section count used in the middle Serre
argument. -/
theorem cubicElevenSelectedEvaluation_ker_finrank_le_one
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (W : Submodule K (grading (equationIdeal p hp) 3))
    [FiniteDimensional K W]
    (hW : finrank K W ≤ 12) :
    finrank K (LinearMap.ker
      (cubicElevenSelectedEvaluation p hp hp0 hprime W)) ≤ 1 := by
  apply eleven_point_maximal_rank_kernel_finrank_le_one
    (K := K) (V := W)
    (W := cubicElevenMaximalRankPoints p hp hp0 hprime W → K)
    (cubicElevenSelectedEvaluation p hp hp0 hprime W)
  · exact hW
  · exact cubicElevenMaximalRankPoints_target_finrank p hp hp0 hprime W
  · exact cubicElevenSelectedEvaluation_maximalRank p hp hp0 hprime W

end PfaffianDescent
