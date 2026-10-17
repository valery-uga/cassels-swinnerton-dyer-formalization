import PfaffianDescent.NativeNegativeTwoPowerFrameTransition
import PfaffianDescent.ActualProjectiveLineDifferentialInverseTransition
import PfaffianDescent.VoisinPositiveTwistTriviality

/- SOURCE ONLY / UNVERIFIED. Original P1 O(-2) frames and literal reciprocal
square coefficient, with all generation and coordinate data derived internally. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type u) [CommRing K]
local notation "Iline" => (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K))

/-- Degree-one generation for ORIGINAL quotient P1, even over a trivial base ring. -/
theorem actualProjectiveLine_irrelevant_le_span_degreeOne :
    (HomogeneousIdeal.irrelevant (grading Iline)).toIdeal ≤
      Ideal.span (Set.range (fun f : grading Iline 1 => (f : CoordinateRing Iline))) := by
  rw [irrelevant_eq_coordinateIdeal]
  apply Ideal.span_mono
  rintro _ ⟨b, rfl⟩
  exact ⟨⟨coordinate Iline b, coordinate_mem Iline b⟩, rfl⟩

/-- Actual negative O(-2) frame of SAME P1 on an original coordinate open. -/
def actualProjectiveLineNegativeTwoRestrictionUnitIso (b : Bool) :
    (Scheme.Modules.restrictFunctor (Proj.basicOpen (grading Iline) (coordinate Iline b)).ι).obj
        (sheafOfModules (grading Iline) 2) ≅
      SheafOfModules.unit
        (Proj.basicOpen (grading Iline) (coordinate Iline b) : Scheme).ringCatSheaf :=
  nativeNegativeTwoPowerFrameRestrictionUnitIso (grading Iline)
    ⟨coordinate Iline b, coordinate_mem Iline b⟩
    (actualProjectiveLine_irrelevant_le_span_degreeOne K)

/-- The normalized scalar in the negative transition is EXACTLY the earlier
original P1 reciprocal coordinate s/t on D_+(s*t). -/
theorem actualProjectiveLine_negativeRatio_eq_overlapTInverse :
    nativeDegreeOneRatioOnSubopen (grading Iline)
      ⟨coordinate Iline true, coordinate_mem Iline true⟩
      ⟨coordinate Iline false, coordinate_mem Iline false⟩
      (actualProjectiveLineCoordinateOverlap K)
      (Proj.basicOpen_mono (grading Iline) (coordinate Iline true)
        (coordinate Iline false * coordinate Iline true)
        ⟨coordinate Iline false, mul_comm _ _⟩) =
      actualProjectiveLineOverlapTInverse K := by
  have h := Proj.awayMap_awayToSection (grading Iline) (coordinate_mem Iline false)
    (mul_comm (coordinate Iline false) (coordinate Iline true))
  change (projectiveLineProj K).presheaf.map _
    ((Proj.awayToSection (grading Iline) (coordinate Iline true)).hom
      (chartCoordinate Iline true false)) = _
  exact (ConcreteCategory.congr_hom h (chartCoordinate Iline true false)).symm

/-- Eliminate ONLY the scalar name at the abstract grading, BEFORE supplying
original P1 factories. The actual caller computes its coefficient internally. -/
private theorem nativeNegativeTwoPowerFrameTransitionNamedCoefficient003
    {A ρ : Type u} [CommRing A] [SetLike ρ A] [AddSubgroupClass ρ A]
    (G : ℕ → ρ) [GradedRing G] (ell eta : G 1)
    (U : (Proj G).Opens) (hU : U ≤ Proj.basicOpen G (ell : A))
    (c : Γ(Proj G, U)) (hc : nativeDegreeOneRatioOnSubopen G ell eta U hU = c)
    (z : Γ(sheafOfModules G 2, U)) :
    (nativeNegativeTwoPowerFrameHom G eta).val.app (op U) z =
      @Mul.mul (Γ(Proj G, U)) (inferInstance : Mul (Γ(Proj G, U)))
        (c ^ 2) ((nativeNegativeTwoPowerFrameHom G ell).val.app (op U) z) := by
  cases hc
  exact nativeNegativeTwoPowerFrameHom_transition G ell eta U hU z

/-- WHOLE original O(-2) section transition with the SAME s/t appearing
in the genuine differential transition D(s/t)=-(s/t)^2 D(t/s). -/
theorem actualProjectiveLineNegativeTwoPowerFrame_transition
    (z : Γ(sheafOfModules (grading Iline) 2, actualProjectiveLineCoordinateOverlap K)) :
    (nativeNegativeTwoPowerFrameHom (grading Iline)
      ⟨coordinate Iline false, coordinate_mem Iline false⟩).val.app
        (op (actualProjectiveLineCoordinateOverlap K)) z =
      @Mul.mul (Γ(projectiveLineProj K, actualProjectiveLineCoordinateOverlap K))
        (inferInstance : Mul (Γ(projectiveLineProj K, actualProjectiveLineCoordinateOverlap K)))
        (actualProjectiveLineOverlapTInverse K ^ 2)
        ((nativeNegativeTwoPowerFrameHom (grading Iline)
          ⟨coordinate Iline true, coordinate_mem Iline true⟩).val.app
            (op (actualProjectiveLineCoordinateOverlap K)) z) := by
  exact nativeNegativeTwoPowerFrameTransitionNamedCoefficient003 (grading Iline)
    (⟨coordinate Iline true, coordinate_mem Iline true⟩ : grading Iline 1)
    (⟨coordinate Iline false, coordinate_mem Iline false⟩ : grading Iline 1)
    (actualProjectiveLineCoordinateOverlap K)
    (Proj.basicOpen_mono (grading Iline) (coordinate Iline true)
      (coordinate Iline false * coordinate Iline true)
      ⟨coordinate Iline false, mul_comm _ _⟩)
    (actualProjectiveLineOverlapTInverse K)
    (actualProjectiveLine_negativeRatio_eq_overlapTInverse K) z

end PfaffianDescent
end
