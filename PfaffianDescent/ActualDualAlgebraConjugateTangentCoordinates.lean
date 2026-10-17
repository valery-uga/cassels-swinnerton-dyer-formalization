import PfaffianDescent.QuarticConjugateJets
import Mathlib.RingTheory.Nilpotent.Basic

/-! Exact relation between the actual dual presentation of a supplied algebra
and the conjugate tangent matrix. Removing a diagonal tangent coefficient is
multiplication by an explicit unit, so all homogeneous nilpotent equations
are retained. -/

noncomputable section
namespace PfaffianDescent
open MvPolynomial Module TrivSqZeroExt
universe u
variable {k L K A : Type u} [Field k] [Field L] [Field K]
  [CommRing A] [Algebra k L] [Algebra k K] [Algebra k A]

/-- The projective diagonal normalization has an explicit inverse. -/
theorem dual_projective_normalization_isUnit (a : K) :
    IsUnit (1 + TrivSqZeroExt.inr (-a) : DualNumber K) := by
  apply IsNilpotent.isUnit_one_add
  refine ⟨2, ?_⟩
  rw [pow_two]
  apply TrivSqZeroExt.ext <;> simp [DualNumber.snd_mul]

/-- These are exact dual coordinates of the GIVEN algebra A. The right side
uses its actual algebra equivalence and its original coordinate evaluator;
the tangent matrix on the left is the one calculated from those same values. -/
theorem actualDual_conjugate_tangent_coordinates
    (eA : A ≃ₐ[k] DualNumber L) (x : Fin 4 → A) (p v : Fin 4 → L)
    (hx : ∀ r, eA (x r) = TrivSqZeroExt.inl (p r) + TrivSqZeroExt.inr (v r))
    (full : Fin 4 ≃ (L →ₐ[k] K))
    (hspan : Submodule.span K
      (Set.range (fun sigma : L →ₐ[k] K => fun r => sigma (p r))) = ⊤)
    (i m : Fin 4) :
    ∑ j, algebraMap K (DualNumber K)
        (QuarticNet.basisCoordinateMatrix (QuarticNet.conjugateBasis full p hspan) m j) *
      QuarticNet.tangentDualPoint (QuarticNet.conjugateTangentMatrix full p v hspan) i j =
      (1 + TrivSqZeroExt.inr (-QuarticNet.conjugateTangentRow full p v hspan i i) :
        DualNumber K) * QuarticNet.dualNumberEmbedding (full i) (eA (x m)) := by
  rw [hx m]
  refine (QuarticNet.conjugate_dual_coordinates full p v hspan i m).trans ?_
  congr 1
  apply TrivSqZeroExt.ext <;> simp only [QuarticNet.dualNumberEmbedding_apply,
    TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl,
    TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr,
    TrivSqZeroExt.fst_mk, TrivSqZeroExt.snd_mk, zero_add, add_zero]

/-- Even one actual residue embedding detects every homogeneous equation of
A, including its nilpotent conditions. This retains the full homogeneous
restriction equations rather than testing reduced support. -/
theorem actualDual_conjugate_tangent_equation_iff
    (eA : A ≃ₐ[k] DualNumber L) (x : Fin 4 → A) (p v : Fin 4 → L)
    (hx : ∀ r, eA (x r) = TrivSqZeroExt.inl (p r) + TrivSqZeroExt.inr (v r))
    (full : Fin 4 ≃ (L →ₐ[k] K))
    (hspan : Submodule.span K
      (Set.range (fun sigma : L →ₐ[k] K => fun r => sigma (p r))) = ⊤)
    (F : MvPolynomial (Fin 4) k) (n : ℕ) (hF : F.IsHomogeneous n) (i : Fin 4) :
    aeval (QuarticNet.tangentDualPoint (QuarticNet.conjugateTangentMatrix full p v hspan) i)
      (linearSubstitution
        (QuarticNet.basisCoordinateMatrix (QuarticNet.conjugateBasis full p hspan))
        (map (algebraMap k K) F)) = 0 ↔ aeval x F = 0 := by
  let c : DualNumber K :=
    1 + TrivSqZeroExt.inr (-QuarticNet.conjugateTangentRow full p v hspan i i)
  let y : Fin 4 → DualNumber K := fun r =>
    QuarticNet.dualNumberEmbedding (full i) (eA (x r))
  have hcoordinates : (fun m => ∑ j, algebraMap K (DualNumber K)
        (QuarticNet.basisCoordinateMatrix (QuarticNet.conjugateBasis full p hspan) m j) *
      QuarticNet.tangentDualPoint (QuarticNet.conjugateTangentMatrix full p v hspan) i j) = c • y := by
    funext m
    exact actualDual_conjugate_tangent_coordinates eA x p v hx full hspan i m
  have hy : aeval y (map (algebraMap k K) F) =
      QuarticNet.dualNumberEmbedding (full i) (eA (aeval x F)) := by
    rw [aeval_def, eval₂_map, ← IsScalarTower.algebraMap_eq k K (DualNumber K)]
    change (aeval (R := k) y) F = _
    exact (comp_aeval_apply x
      ((QuarticNet.dualNumberEmbedding (full i)).comp eA.toAlgHom) F).symm
  rw [QuarticNet.aeval_linearSubstitution, hcoordinates,
    QuarticNet.aeval_smul_of_homogeneous _ n (hF.map (algebraMap k K)), hy]
  have hc : IsUnit (c ^ n) :=
    (dual_projective_normalization_isUnit
      (QuarticNet.conjugateTangentRow full p v hspan i i)).pow n
  have hinj : Function.Injective (QuarticNet.dualNumberEmbedding (full i)) := by
    intro a b hab
    apply TrivSqZeroExt.ext
    · exact (full i).injective (congrArg TrivSqZeroExt.fst hab)
    · exact (full i).injective (congrArg TrivSqZeroExt.snd hab)
  constructor
  · intro hz
    have hjet : QuarticNet.dualNumberEmbedding (full i) (eA (aeval x F)) = 0 :=
      hc.mul_left_cancel (by simpa using hz)
    have hA : eA (aeval x F) = 0 :=
      hinj (hjet.trans ((QuarticNet.dualNumberEmbedding (full i)).map_zero).symm)
    exact eA.injective (hA.trans eA.map_zero.symm)
  · intro hz
    rw [hz]
    have hzA : eA (0 : A) = 0 := eA.map_zero
    rw [hzA, map_zero, mul_zero]

end PfaffianDescent
