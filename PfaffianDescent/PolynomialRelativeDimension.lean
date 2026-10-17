import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (R : Type u) [CommRing R] (ι : Type) [Finite ι]

/-- The empty relation list gives the standard smooth presentation of affine space. -/
noncomputable def polynomialSubmersivePresentation :
    Algebra.SubmersivePresentation R (MvPolynomial ι R) ι Empty where
  toGenerators := Algebra.Generators.mvPolynomial R ι
  relation := Empty.elim
  span_range_relation_eq_ker := by
    rw [Algebra.Generators.ker_mvPolynomial]
    simp
  map := Empty.elim
  map_inj := Function.injective_of_subsingleton _
  jacobian_isUnit := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    simp

lemma polynomialSubmersivePresentation_dimension :
    (polynomialSubmersivePresentation R ι).dimension = Nat.card ι := by
  simp [Algebra.Presentation.dimension]

lemma polynomial_standardSmooth_relative_dimension :
    Algebra.IsStandardSmoothOfRelativeDimension (Nat.card ι) R (MvPolynomial ι R) :=
  (polynomialSubmersivePresentation R ι).isStandardSmoothOfRelativeDimension
    (polynomialSubmersivePresentation_dimension R ι)

/-- Affine space with `ι` coordinates is smooth of relative dimension `card ι`. -/
lemma polynomial_smooth_relative_dimension :
    SmoothOfRelativeDimension (Nat.card ι)
      (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial ι R)))) := by
  apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension (Nat.card ι))).mpr
  apply RingHom.locally_of (RingHom.isStandardSmoothOfRelativeDimension_respectsIso)
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (Nat.card ι)).mpr
    (polynomial_standardSmooth_relative_dimension R ι)

end
end PfaffianDescent
