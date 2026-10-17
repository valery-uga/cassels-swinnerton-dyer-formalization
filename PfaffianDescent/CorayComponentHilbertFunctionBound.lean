import PfaffianDescent.CorayCurveHilbertPolynomial
import PfaffianDescent.CorayProjectiveIntersectionChartDimension
import PfaffianDescent.HomogeneousQuotientMap
import Lean.Elab.Tactic.Omega

/-!
# Actual homogeneous component quotient and original p/q Hilbert-function bound

Construct the degreewise map of the SAME homogeneous coordinate rings and prove
surjectivity from actual homogeneous polynomial preimages. Its finite dimension
bound applies the actual original p/q Koszul Hilbert identity to every actual
component/subscheme quotient. It assumes no degree or Hilbert slope certificate.
It is NOT yet prime multiplicity additivity or the rμ≤3l theorem.
SOURCE ONLY / UNVERIFIED: root owns compiler/audit.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Restrict the actual coordinate-ring quotient to its actual degree-d parts. -/
def homogeneousCoordinateQuotientGradeMap
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hIJ : I.toIdeal ≤ J.toIdeal) (d : ℕ) : grading I d →ₗ[K] grading J d where
  toFun x := ⟨(Ideal.Quotient.factorₐ K hIJ) x.1,
    PfaffianDescent.coordinateQuotientMap_mem I J hIJ x.2⟩
  map_add' x y := Subtype.ext (map_add (Ideal.Quotient.factorₐ K hIJ) x.1 y.1)
  map_smul' a x := Subtype.ext (map_smul (Ideal.Quotient.factorₐ K hIJ) a x.1)

/-- Every actual homogeneous target class has the SAME homogeneous polynomial
as a preimage. Whole-ring surjectivity alone is not used as a grade certificate. -/
theorem homogeneousCoordinateQuotientGradeMap_surjective
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hIJ : I.toIdeal ≤ J.toIdeal) (d : ℕ) :
    Function.Surjective (homogeneousCoordinateQuotientGradeMap I J hIJ d) := by
  intro y
  obtain ⟨q, hqd, hq⟩ := y.2
  refine ⟨⟨Ideal.Quotient.mk I.toIdeal q, ⟨q, hqd, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  change Ideal.Quotient.mk J.toIdeal q = y.1
  exact hq

/-- Actual inclusion of homogeneous ideals bounds every actual quotient
Hilbert function. The necessary finite-dimensional source is derived from
finite homogeneous polynomial pieces and the actual quotient image. -/
theorem homogeneousCoordinateQuotientGrade_finrank_le
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hIJ : I.toIdeal ≤ J.toIdeal) (d : ℕ) :
    finrank K (grading J d) ≤ finrank K (grading I d) := by
  letI : Module.Finite K (grading I d) := by
    change Module.Finite K ((homogeneousSubmodule (Fin 4) K d).map
      (Ideal.Quotient.mkₐ K I.toIdeal).toLinearMap)
    infer_instance
  exact LinearMap.finrank_le_finrank_of_surjective
    (homogeneousCoordinateQuotientGradeMap_surjective I J hIJ d)

/-- An ACTUAL homogeneous component/subscheme of the ORIGINAL selected smooth
cubic/degree-n intersection satisfies its literal linear Hilbert-function upper
bound in every degree ≥n+3. This proves no component degree/genus premise. -/
theorem selectedProjectiveComponent_hilbertFunction_linearBound
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 1 ≤ n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hIC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal) (d : ℕ) :
    2 * finrank K (grading C (d + n + 3)) + 3 * n * (n - 1) ≤
      6 * n * (d + n + 3) := by
  let I := projectiveIntersectionIdeal p q hp hq
  have hle := homogeneousCoordinateQuotientGrade_finrank_le I C hIC (d + n + 3)
  have hgrade : finrank K (grading I (d + n + 3)) =
      finrank K (curveComponent p q (d + n + 3)) := by
    exact congrArg
      (fun J : Ideal (MvPolynomial (Fin 4) K) =>
        finrank K ((homogeneousSubmodule (Fin 4) K (d + n + 3)).map
          (Ideal.Quotient.mkₐ K J).toLinearMap))
      (projectiveIntersectionIdeal_toIdeal p q hp hq)
  rw [hgrade] at hle
  have hrel := isRelPrime_of_smooth_cubic_and_not_mem p q hp hp0 hnot
  have hwhole := curve_hilbert_polynomial_identity_of_positive_degree
    p q hp hq hp0 hrel hn d
  have htwo := Nat.mul_le_mul_left 2 hle
  omega

end PfaffianDescent.Coray
