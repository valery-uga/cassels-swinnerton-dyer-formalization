import PfaffianDescent.ConjugateRescaledRelabelActualGaloisAction
import PfaffianDescent.QuarticGaloisMatching
import PfaffianDescent.QuarticConjugateSpan
import PfaffianDescent.QuarticTangentRescaling

/-! SOURCE ONLY, UNVERIFIED. Matching branch on the SAME supplied algebra
coordinates: actual equation transport gives both line restrictions, and
indexed conjugates derive the Galois action needed by genuine pair descent.
The matching entry conditions are this branch's scalar normal form, not a
supplied graph/action or finite-base certificate. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open MvPolynomial Module TrivSqZeroExt
universe u
variable {k L K A : Type u} [Field k] [Field L] [Field K] [CommRing A]
  [Algebra k L] [Algebra k K] [Algebra k A]

theorem originalDualCoordinates_matching_lines_and_galois_point
    [IsGalois k K] [IsAlgClosed K]
    [FiniteDimensional k L] [Algebra.IsSeparable k L]
    (eA : A ≃ₐ[k] DualNumber L) (x : Fin 4 → A)
    (b : Basis (Fin 4) k L) (v : Fin 4 → L)
    (hx : ∀ m, eA (x m) = TrivSqZeroExt.inl (b m) + TrivSqZeroExt.inr (v m))
    (full : Fin 4 ≃ (L →ₐ[k] K))
    (l : Fin 4 → K) (hl : ∀ m, l m ≠ 0) (pi : Equiv.Perm (Fin 4))
    (hskew : ∀ i j,
      tangentRelabel (rescaleTangentDirections l
        (conjugateTangentMatrix full b v (conjugate_basis_span b full))) pi i j =
      -tangentRelabel (rescaleTangentDirections l
        (conjugateTangentMatrix full b v (conjugate_basis_span b full))) pi j i)
    (h01 : tangentRelabel (rescaleTangentDirections l
      (conjugateTangentMatrix full b v (conjugate_basis_span b full))) pi 0 1 ≠ 0)
    (h23 : tangentRelabel (rescaleTangentDirections l
      (conjugateTangentMatrix full b v (conjugate_basis_span b full))) pi 2 3 ≠ 0)
    (h02 : tangentRelabel (rescaleTangentDirections l
      (conjugateTangentMatrix full b v (conjugate_basis_span b full))) pi 0 2 = 0)
    (h03 : tangentRelabel (rescaleTangentDirections l
      (conjugateTangentMatrix full b v (conjugate_basis_span b full))) pi 0 3 = 0)
    (h12 : tangentRelabel (rescaleTangentDirections l
      (conjugateTangentMatrix full b v (conjugate_basis_span b full))) pi 1 2 = 0)
    (h13 : tangentRelabel (rescaleTangentDirections l
      (conjugateTangentMatrix full b v (conjugate_basis_span b full))) pi 1 3 = 0)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hFx : aeval (R := k) x F = 0) :
    let B := (conjugateBasis full b (conjugate_basis_span b full)).reindex pi.symm
    let G := linearSubstitution (basisCoordinateMatrix B) (map (algebraMap k K) F)
    (coordinateLineRestriction G = 0 ∧ coordinateLineRestriction23 G = 0) ∧
      (∃ p : Fin 4 → k, p ≠ 0 ∧ aeval p F = 0) := by
  let hs := conjugate_basis_span b full
  let U0 := conjugateTangentMatrix full b v hs
  let U := tangentRelabel (rescaleTangentDirections l U0) pi
  let B := (conjugateBasis full b hs).reindex pi.symm
  let G := linearSubstitution (basisCoordinateMatrix B) (map (algebraMap k K) F)
  have hdual : aeval (R := k) (fun m => TrivSqZeroExt.inl (b m) +
      TrivSqZeroExt.inr (v m)) F = (0 : DualNumber L) := by
    have hcoords : (fun m => eA (x m)) =
        (fun m => TrivSqZeroExt.inl (b m) + TrivSqZeroExt.inr (v m)) := funext hx
    have hEval := comp_aeval_apply x eA.toAlgHom F
    change eA (aeval (R := k) x F) = aeval (R := k) (fun m => eA (x m)) F at hEval
    rw [← hcoords]
    exact hEval.symm.trans ((congrArg eA hFx).trans (map_zero eA))
  have hvan0 := homogeneous_jet_vanishes_on_conjugates full b v hs F 3 hF hdual
  have hvan1 := rescaleTangentDirections_vanishing U0 l
    (linearSubstitution (basisCoordinateMatrix (conjugateBasis full b hs))
      (map (algebraMap k K) F)) hvan0
  have hvan := tangentRelabel_vanishing (conjugateBasis full b hs)
    (rescaleTangentDirections l U0) pi (map (algebraMap k K) F) hvan1
  have hdiag (i : Fin 4) : U i i = 0 := by
    simp only [U, U0, tangentRelabel, rescaleTangentDirections,
      conjugateTangentMatrix_diagonal, mul_zero]
  have hU : U = skewTangentDirections (U 0 1) 0 0 0 0 (U 2 3) := by
    have h := skew_matrix_eq_parameters U hdiag hskew
    simpa only [U, U0, hs, h02, h03, h12, h13] using h
  have hvan' : ∀ r, aeval (tangentDualPoint (skewTangentDirections
      (U 0 1) 0 0 0 0 (U 2 3)) r) G = 0 := by
    simpa only [← hU] using hvan
  have hlines := cubic_contains_matching_lines_of_skew_matrix
    (U 0 1) (U 2 3) h01 h23 G
    (linearSubstitution_homogeneous _ (hF.map (algebraMap k K))) hvan'
  have hact := conjugate_rescaled_relabel_actual_galois_action full b v hs l hl pi
  have hact' : ∀ g : K ≃ₐ[k] K, ∃ rho : Equiv.Perm (Fin 4),
      (∀ i m, g (B i m) = B (rho i) m) ∧
      (∀ i j, skewTangentDirections (U 0 1) 0 0 0 0 (U 2 3) i j ≠ 0 ↔
        skewTangentDirections (U 0 1) 0 0 0 0 (U 2 3) (rho i) (rho j) ≠ 0) := by
    simpa only [← hU] using hact
  exact ⟨hlines, cubic_point_from_galois_matching B (U 0 1) (U 2 3)
    h01 F hF hvan' hact'⟩

end PfaffianDescent.QuarticNet
