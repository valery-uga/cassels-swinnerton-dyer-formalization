import PfaffianDescent.CorayStabilizerHomogeneousIdealDescent
import AllCharacteristics.ProjectiveBaseChange

/-! Actual projective scheme descent over the internally constructed
stabilizer fixed field, using checked WHOLE-IDEAL trace descent. No supplied
map-comap equality or base-change certificate. Does not assert geometric
integrality or identify a projective geometric component. Source only. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
universe u
variable {K E : Type u} [Field K] [Field E] [Algebra K E]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Actual Cartesian descent square for the constructed homogeneous prime
contraction over its actual stabilizer fixed field. -/
theorem homogeneousPrime_stabilizerFixedField_projective_isPullback
    [FiniteDimensional K E] [IsGalois K E]
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) E))
    [C.toIdeal.IsPrime] :
    let L := homogeneousIdealStabilizerFixedField (K := K) C
    let D := C.comap (componentPolynomialCoefficientMap (algebraMap L E))
    let h := (homogeneousPrime_stabilizerFixedField_descends (K := K) C).2
    IsPullback (projectiveCoefficientMap (algebraMap L E) D C h)
      (toBase C) (toBase D) (Spec.map (CommRingCat.ofHom (algebraMap L E))) := by
  exact isPullback_projectiveCoefficientMap _ _ _ _

/-- The actual whole projective scheme is the coefficient base change of the
actual homogeneous contraction over its constructed stabilizer fixed field. -/
def homogeneousPrime_stabilizerFixedField_projectiveBaseChangeIso
    [FiniteDimensional K E] [IsGalois K E]
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) E))
    [C.toIdeal.IsPrime] :
    let L := homogeneousIdealStabilizerFixedField (K := K) C
    let D := C.comap (componentPolynomialCoefficientMap (algebraMap L E))
    scheme C ≅ pullback (toBase D)
      (Spec.map (CommRingCat.ofHom (algebraMap L E))) :=
  (homogeneousPrime_stabilizerFixedField_projective_isPullback (K := K) C).isoPullback

end PfaffianDescent.Coray
