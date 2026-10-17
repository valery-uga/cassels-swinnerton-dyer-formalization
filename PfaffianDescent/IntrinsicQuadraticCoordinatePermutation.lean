import PfaffianDescent.AmbientNormalizedPointChartComparison
import PfaffianDescent.AmbientProjectiveRenameChartSquare
import PfaffianDescent.PolynomialLinearChange
import Mathlib.LinearAlgebra.Matrix.Permutation

/-! Actual coordinate permutation of the FULL quadratic series. The chart
point is the original embedding with its original algebra, including nilpotents. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module Matrix
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem ambientNormalizedCoordinateChartPoint_intrinsicQuadratics
    {K A : Type u} [Field K] [CommRing A] [Algebra K A] [Module.Finite K A]
    (x : Fin 4 → A) (j : Fin 4) (hx : x j = 1) :
    intrinsicFullQuadraticSystem (ambientNormalizedCoordinateChartPoint (F := K) x j hx) =
      homogeneousVanishingPolynomialSubmodule (K := K) x 2 := by
  have he : ∀ p ∈ (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)).toIdeal,
      p.eval₂ (algebraMap K A) x = 0 := by
    intro p hp
    simp [Ideal.mem_bot.mp hp]
  rw [← linearNormalizedPoint_toAmbient_eq_coordinateChartPoint ⊥ x j hx he]
  exact linearNormalizedPoint_intrinsicQuadraticSystem_eq_evaluation_of_unit_coordinate
    ⊥ x (X j) (isHomogeneous_X K j) (by simpa only [eval₂_X] using hx)
    he j 1 hx.symm

theorem homogeneousVanishingPolynomialSubmodule_rename
    {K A : Type u} [Field K] [CommRing A] [Algebra K A] [Module.Finite K A]
    (x : Fin 4 → A) (pi : Equiv.Perm (Fin 4)) (d : ℕ) :
    (homogeneousVanishingPolynomialSubmodule (K := K) x d).map
      (renameEquiv K pi.symm).toLinearEquiv.toLinearMap =
      homogeneousVanishingPolynomialSubmodule (K := K) (fun r => x (pi r)) d := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨hqhom, hqzero⟩ :=
      (mem_homogeneousVanishingPolynomialSubmodule_iff x d q).mp hq
    apply (mem_homogeneousVanishingPolynomialSubmodule_iff _ d _).mpr
    refine ⟨hqhom.rename_isHomogeneous, ?_⟩
    change aeval (R := K) (fun r => x (pi r)) (rename pi.symm q) = 0
    simpa only [aeval_def, eval₂_rename, Function.comp_def,
      pi.apply_symm_apply] using hqzero
  · intro hp
    obtain ⟨hphom, hpzero⟩ :=
      (mem_homogeneousVanishingPolynomialSubmodule_iff _ d p).mp hp
    refine ⟨rename pi p, ?_, ?_⟩
    · apply (mem_homogeneousVanishingPolynomialSubmodule_iff x d _).mpr
      refine ⟨hphom.rename_isHomogeneous, ?_⟩
      change aeval (R := K) x (rename pi p) = 0
      simpa only [aeval_def, eval₂_rename, Function.comp_def] using hpzero
    · exact (renameEquiv K pi).symm_apply_apply p

theorem permutationMatrix_isUnit_det {K : Type u} [Field K]
    (pi : Equiv.Perm (Fin 4)) : IsUnit (pi.permMatrix K).det := by
  apply Matrix.isUnit_det_of_right_inverse (B := Equiv.Perm.permMatrix K pi.symm)
  change pi.permMatrix K * (pi⁻¹).permMatrix K = 1
  exact (Matrix.permMatrix_mul (pi⁻¹) pi).symm.trans (by simp)

theorem linearSubstitution_permutationMatrix {K : Type u} [Field K]
    (pi : Equiv.Perm (Fin 4)) :
    linearSubstitution (pi.permMatrix K) = (renameEquiv K pi).toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro r
  rw [linearSubstitution_X, AlgEquiv.toAlgHom_apply, renameEquiv_apply, rename_X]
  change ((pi.permMatrix K).map C).mulVec X r = X (pi r)
  simpa only [PEquiv.map_toMatrix C pi.toPEquiv, Matrix.permMatrix_mulVec,
    Function.comp_def]

/-- The inverse permutation transports equations in the same orientation
as the subsequent residue-basis substitution. -/
theorem ambientNormalizedCoordinateChartPoint_intrinsicQuadratics_permutation
    {K A : Type u} [Field K] [CommRing A] [Algebra K A] [Module.Finite K A]
    (x : Fin 4 → A) (j : Fin 4) (hx : x j = 1)
    (pi : Equiv.Perm (Fin 4)) (hpi : pi 0 = j) :
    (intrinsicFullQuadraticSystem
      (ambientNormalizedCoordinateChartPoint (F := K) x j hx)).map
        (linearSubstitutionEquiv (Equiv.Perm.permMatrix K pi.symm)
          (permutationMatrix_isUnit_det pi.symm)).toLinearEquiv.toLinearMap =
      intrinsicFullQuadraticSystem
        (ambientNormalizedCoordinateChartPoint (F := K) (fun r => x (pi r)) 0
          (by rw [hpi]; exact hx)) := by
  rw [ambientNormalizedCoordinateChartPoint_intrinsicQuadratics,
    ambientNormalizedCoordinateChartPoint_intrinsicQuadratics]
  have he : (linearSubstitutionEquiv (Equiv.Perm.permMatrix K pi.symm)
      (permutationMatrix_isUnit_det pi.symm)).toLinearEquiv.toLinearMap =
      (renameEquiv K pi.symm).toLinearEquiv.toLinearMap := by
    apply LinearMap.ext
    intro p
    change linearSubstitution (Equiv.Perm.permMatrix K pi.symm) p = rename pi.symm p
    exact DFunLike.congr_fun
      (linearSubstitution_permutationMatrix (K := K) pi.symm) p
  rw [he]
  exact homogeneousVanishingPolynomialSubmodule_rename x pi 2

end PfaffianDescent
