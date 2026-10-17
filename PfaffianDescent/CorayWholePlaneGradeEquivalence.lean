import PfaffianDescent.CorayWholePlaneGradedQuotient
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! SOURCE ONLY / UNCOMPILED156. Every-grade equivalence of ENTIRE quotient
rings, induced by the SAME explicit155 maps and original coefficient actions. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual inverse whole quotient maps preserve every actual grade and
its original coefficient-field scalar action. -/
def wholePlaneCoordinateGradeLinearEquiv
    (t : Fin 3 → K) (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hH : Ideal.span ({planeHyperplaneRelation t} : Set (MvPolynomial (Fin 4) K)) ≤ I.toIdeal)
    (d : ℕ) :
    grading I d ≃ₗ[K] grading (wholePlaneRestrictionIdeal t I) d where
  toFun x := ⟨wholePlaneQuotientRestriction t I x.val,
    (wholePlaneGradedRestriction t I).map_mem x.property⟩
  invFun y := ⟨wholePlaneQuotientInclusion t I hH y.val,
    (wholePlaneGradedInclusion t I hH).map_mem y.property⟩
  left_inv x := Subtype.ext
    (AlgHom.congr_fun (wholePlaneQuotientInclusion_comp_restriction t I hH) x.val)
  right_inv y := Subtype.ext
    (AlgHom.congr_fun (wholePlaneQuotientRestriction_comp_inclusion t I hH) y.val)
  map_add' x y := Subtype.ext (map_add (wholePlaneQuotientRestriction t I) x.val y.val)
  map_smul' c x := Subtype.ext (map_smul (wholePlaneQuotientRestriction t I) c x.val)

/-- Native whole quotient-grade ranks agree, including nilpotent contributions. -/
theorem wholePlaneCoordinateGrade_finrank_eq
    (t : Fin 3 → K) (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hH : Ideal.span ({planeHyperplaneRelation t} : Set (MvPolynomial (Fin 4) K)) ≤ I.toIdeal)
    (d : ℕ) :
    finrank K (grading I d) = finrank K (grading (wholePlaneRestrictionIdeal t I) d) :=
  (wholePlaneCoordinateGradeLinearEquiv t I hH d).finrank_eq

end PfaffianDescent.Coray
