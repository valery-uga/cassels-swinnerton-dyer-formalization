import PfaffianDescent.VoisinDegreeElevenSerreIncidenceKernelScheme
import AllCharacteristics.ProjectiveBaseChange

/-! # Coefficient change preserves the literal six homogeneous evaluation equations -/
noncomputable section
open MvPolynomial
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

lemma serreIncidenceKernelCoordinate_map
    {R E : Type u} [CommRing R] [CommRing E] (g : R →+* E)
    (A : Matrix (Fin 6) (Fin 9) R) (i : Fin 6) :
    MvPolynomial.map g (rectangularLinearCoordinate A i) =
      rectangularLinearCoordinate (A.map g) i := by
  simp [rectangularLinearCoordinate, Matrix.mulVec, dotProduct]

theorem serreIncidenceKernelIdeal_coefficient
    {R E : Type u} [CommRing R] [CommRing E] (g : R →+* E)
    (A : Matrix (Fin 6) (Fin 9) R) :
    (serreEvaluationHomogeneousIdeal A).toIdeal.map (MvPolynomial.map g) =
      (serreEvaluationHomogeneousIdeal (A.map g)).toIdeal := by
  change (Ideal.span (Set.range (rectangularLinearCoordinate A))).map (MvPolynomial.map g) =
    Ideal.span (Set.range (rectangularLinearCoordinate (A.map g)))
  rw [Ideal.map_span]
  congr 1
  ext p
  constructor
  · rintro ⟨q, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (serreIncidenceKernelCoordinate_map g A i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨rectangularLinearCoordinate A i, ⟨i, rfl⟩,
      serreIncidenceKernelCoordinate_map g A i⟩

end PfaffianDescent
