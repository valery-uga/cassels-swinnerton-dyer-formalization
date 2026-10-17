import PfaffianDescent.DehomogenizedQuadricsRelativePrime
import PfaffianDescent.VoisinGenericFourLineDirections
import PfaffianDescent.VoisinQuadraticLineInterpolation

/-!
# Evaluating split-line roots in the standard affine chart

These lemmas connect homogeneous quadratic evaluations on projective roots
to the affine line interpolation argument.
-/

namespace PfaffianDescent

open MvPolynomial

universe u

theorem eval_dehomogenizeAtZero
    {L : Type u} [Field L] (Q : MvPolynomial (Fin 4) L)
    (v : Fin 3 → L) :
    (QuarticNet.dehomogenizeAtZero Q).eval v =
      Q.eval ![(1 : L), v 0, v 1, v 2] := by
  have hcomp : (MvPolynomial.aeval v).comp
      (QuarticNet.dehomogenizeAtZero (k := L)) =
        MvPolynomial.aeval ![(1 : L), v 0, v 1, v 2] := by
    ext i : 1
    fin_cases i <;> simp [QuarticNet.dehomogenizeAtZero]
  have h := congrArg
    (fun f : MvPolynomial (Fin 4) L →ₐ[L] L => f Q) hcomp
  simpa only [AlgHom.comp_apply, MvPolynomial.aeval_eq_eval] using h

theorem dehomogenized_quadric_totalDegree_le_two
    {L : Type u} [Field L] (Q : MvPolynomial (Fin 4) L)
    (hQ : Q.totalDegree ≤ 2) :
    (QuarticNet.dehomogenizeAtZero Q).totalDegree ≤ 2 :=
  (QuarticNet.totalDegree_dehomogenizeAtZero_le Q).trans hQ

def affineLineDirection
    {L : Type u} [Field L] (i j : Fin 2) : Fin 3 → L :=
  fun k => lineDirection i j k.succ

theorem affineLineDirection_chart_vector
    {L : Type u} [Field L] (i j : Fin 2) (s : L) :
    ![(1 : L), s * affineLineDirection i j 0,
      s * affineLineDirection i j 1,
      s * affineLineDirection i j 2] =
      (Pi.single 0 1 : Fin 4 → L) + s • lineDirection i j := by
  funext m
  fin_cases i <;> fin_cases j <;> fin_cases m <;>
    simp [affineLineDirection, lineDirection, Pi.smul_apply]

theorem dehomogenized_quadric_zero_at_normalized_fourLine_root
    {L : Type u} [Field L]
    (Q : MvPolynomial (Fin 4) L) (hQ : Q.IsHomogeneous 2)
    (i j : Fin 2) (t : L) (ht : t ≠ 0)
    (hroot : Q.eval
      (t • (Pi.single 0 1 : Fin 4 → L) + lineDirection i j) = 0) :
    (QuarticNet.dehomogenizeAtZero Q).eval
      (t⁻¹ • affineLineDirection i j) = 0 := by
  rw [eval_dehomogenizeAtZero]
  have hchart :
      ![(1 : L), (t⁻¹ • affineLineDirection i j) 0,
        (t⁻¹ • affineLineDirection i j) 1,
        (t⁻¹ • affineLineDirection i j) 2] =
        t⁻¹ • (t • (Pi.single 0 1 : Fin 4 → L) + lineDirection i j) := by
    rw [fourLine_root_normalization i j t ht]
    simpa only [Pi.smul_apply, smul_eq_mul] using
      (affineLineDirection_chart_vector i j t⁻¹)
  rw [hchart]
  change Q.eval₂ (RingHom.id L)
    (t⁻¹ • (t • (Pi.single 0 1 : Fin 4 → L) + lineDirection i j)) = 0
  rw [AllCharacteristics.eval₂_homogeneous_smul Q hQ]
  simp [hroot]

/-- Three distinct generic roots on one split line force a homogeneous
quadric through them to vanish on the entire affine part of that line. -/
theorem dehomogenized_quadric_zero_on_fourLine_of_three_roots
    {L : Type u} [Field L]
    (Q : MvPolynomial (Fin 4) L) (hQ : Q.IsHomogeneous 2)
    (i j : Fin 2) (t : Fin 3 → L)
    (hinj : Function.Injective t)
    (ht : ∀ k, t k ≠ 0)
    (hroot : ∀ k, Q.eval
      (t k • (Pi.single 0 1 : Fin 4 → L) + lineDirection i j) = 0) :
    ∀ s : L, (QuarticNet.dehomogenizeAtZero Q).eval
      (s • affineLineDirection i j) = 0 := by
  apply affine_quadratic_zero_on_line_of_three_distinct_roots
    (QuarticNet.dehomogenizeAtZero Q)
    (dehomogenized_quadric_totalDegree_le_two Q hQ.totalDegree_le)
    (affineLineDirection i j) (fun k => (t k)⁻¹)
  · exact inv_injective.comp hinj
  · intro k
    exact dehomogenized_quadric_zero_at_normalized_fourLine_root
      Q hQ i j (t k) (ht k) (hroot k)

end PfaffianDescent
