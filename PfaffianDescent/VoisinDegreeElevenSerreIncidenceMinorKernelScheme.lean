import PfaffianDescent.VoisinDegreeElevenSerreIncidencePivotColumns
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceKernelSchemeProjection

/-! # An actual invertible evaluation minor produces the open kernel family -/
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The split matrices and actual projective-plane isomorphism are constructed
internally from the literal six-column unit minor. -/
theorem serreEvaluationKernel_exists_planeIso_of_unit_minor
    {R : Type u} [CommRing R]
    (A : Matrix (Fin 6) (Fin 9) R) (m : Fin 6 ↪ Fin 9)
    (hm : IsUnit (A.submatrix id m).det) :
    ∃ e : scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) R)) ≅
        scheme (serreEvaluationHomogeneousIdeal A),
      e.hom ≫ toBase (serreEvaluationHomogeneousIdeal A) =
        toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) R)) ∧
      IsOpenMap (toBase (serreEvaluationHomogeneousIdeal A)) := by
  obtain ⟨M, N, D, hAM, hNM, hsplit⟩ :=
    serreEvaluationMatrix_exists_split_of_unit_minor A m hm
  exact ⟨serreKernelEquationsSchemeIso A M N D hAM hNM hsplit,
    serreKernelEquationsSchemeIso_hom_toBase A M N D hAM hNM hsplit,
    serreKernelEquationsToBase_isOpenMap A M N D hAM hNM hsplit⟩

end PfaffianDescent
