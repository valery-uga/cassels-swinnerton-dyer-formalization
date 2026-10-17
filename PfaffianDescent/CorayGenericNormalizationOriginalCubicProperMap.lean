import PfaffianDescent.CorayFiniteSchemeGenericNormalization
import PfaffianDescent.CorayCubicSecondEquationActualCurveUnit
import AllCharacteristics.CyclePushforward
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! The SAME canonical normalization maps finitely and properly to the
ORIGINAL cubic. Its composite to Spec K is the SAME original projection.
The original curve immersion preserves each own point's actual residue
field/degree. No properness or coefficient-compatibility premise is supplied.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory AllCharacteristics
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual finite/proper projection of the OWN canonical normalization to
the ORIGINAL cubic, with exact ORIGINAL K structure-map compatibility. -/
theorem projectiveIntersection_genericNormalization_to_originalCubic_finite_proper_and_toBase
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (n : ℕ) (hq : q.IsHomogeneous n)
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let i := cubicSecondEquationCurveImmersion p q hp n hq
    IsFinite (nu ≫ i) ∧ IsProper (nu ≫ i) ∧
      (nu ≫ i) ≫ hypersurfaceToBase p hp = nu ≫ toBase I := by
  intro I X nu i
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  letI : LocallyOfFiniteType (toBase I) := inferInstance
  letI : IsFinite nu := integralScheme_genericNormalization_isFinite X (toBase I)
  letI : IsClosedImmersion i := cubicSecondEquationCurveImmersion_isClosedImmersion p q hp n hq
  refine ⟨inferInstance, inferInstance, ?_⟩
  rw [Category.assoc, cubicSecondEquationCurveImmersion_toBase]

/-- The actual original curve point has the SAME full K-residue degree as
its actual image on the cubic. Residue-map isomorphism is derived from the
OWN canonical closed immersion, never assumed as a degree certificate. -/
theorem projectiveIntersection_originalClosedPoint_degree_eq_originalCubicImage_degree
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (n : ℕ) (hq : q.IsHomogeneous n)
    (P : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq))) :
    (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1 =
      (hypersurfaceToBase p hp).residueDegree
        (cubicSecondEquationCurveImmersion p q hp n hq P.1) := by
  let i := cubicSecondEquationCurveImmersion p q hp n hq
  letI : IsIso (i.residueFieldMap P.1) := isIso_residueFieldMap_of_surjectiveOnStalks i P.1
  have h := residueDegree_comp_of_residueFieldMap_isIso i (hypersurfaceToBase p hp) P.1
  rw [cubicSecondEquationCurveImmersion_toBase] at h
  exact h

end PfaffianDescent.Coray
