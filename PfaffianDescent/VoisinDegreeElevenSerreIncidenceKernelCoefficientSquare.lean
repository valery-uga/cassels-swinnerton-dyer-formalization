import PfaffianDescent.VoisinDegreeElevenSerreIncidenceKernelCoefficientIdeal
import PfaffianDescent.HomogeneousQuotientMap

/-! # Actual kernel immersion and coefficient change commute -/
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceKernelImmersion_coefficient_square
    {R E : Type u} [CommRing R] [CommRing E] (g : R →+* E)
    (A : Matrix (Fin 6) (Fin 9) R) :
    schemeQuotientMap (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) E))
        (serreEvaluationHomogeneousIdeal (A.map g)) bot_le ≫
      projectiveCoefficientMap g
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) R))
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) E)) (by simp) =
    projectiveCoefficientMap g (serreEvaluationHomogeneousIdeal A)
        (serreEvaluationHomogeneousIdeal (A.map g)) (serreIncidenceKernelIdeal_coefficient g A) ≫
      schemeQuotientMap (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) R))
        (serreEvaluationHomogeneousIdeal A) bot_le := by
  unfold schemeQuotientMap projectiveCoefficientMap
  rw [← Proj.map_comp, ← Proj.map_comp]
  congr 1
  apply GradedRingHom.ext
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

end PfaffianDescent
