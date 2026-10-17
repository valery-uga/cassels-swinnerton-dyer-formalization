import PfaffianDescent.VoisinDegreeElevenSerreIncidenceKernelEquations
import PfaffianDescent.GradedSurjection

/-! # The actual split evaluation-kernel scheme is a projective plane -/
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
variable {R : Type u} [CommRing R]

def serreEvaluationHomogeneousIdeal (A : Matrix (Fin 6) (Fin 9) R) :
    HomogeneousIdeal (homogeneousSubmodule (Fin 9) R) :=
  ⟨serreEvaluationEquationIdeal A, Ideal.homogeneous_span _ _ (by
    rintro _ ⟨i, rfl⟩
    exact ⟨1, rectangularLinearCoordinate_homogeneous A i⟩)⟩

def serreKernelEquationsGradedMap
    (A : Matrix (Fin 6) (Fin 9) R) (M : Matrix (Fin 9) (Fin 3) R)
    (hAM : A * M = 0) :
    grading (serreEvaluationHomogeneousIdeal A) →+*ᵍ
      grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) R)) :=
  polynomialQuotientGradingMap _ _ (rectangularSubstitution M)
    (serreEvaluationEquationIdeal_le_ker A M hAM)
    (fun _ _ hp => rectangularSubstitution_homogeneous M hp)

def serreKernelEquationsGradedInverse
    (A : Matrix (Fin 6) (Fin 9) R) (N : Matrix (Fin 3) (Fin 9) R) :
    grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) R)) →+*ᵍ
      grading (serreEvaluationHomogeneousIdeal A) :=
  polynomialQuotientGradingMap _ _ (rectangularSubstitution N) bot_le
    (fun _ _ hp => rectangularSubstitution_homogeneous N hp)

lemma serreKernelEquationsGraded_comp_inverse
    (A : Matrix (Fin 6) (Fin 9) R) (M : Matrix (Fin 9) (Fin 3) R)
    (N : Matrix (Fin 3) (Fin 9) R) (hAM : A * M = 0) (hNM : N * M = 1) :
    (serreKernelEquationsGradedMap A M hAM).comp
      (serreKernelEquationsGradedInverse A N) = GradedRingHom.id _ := by
  apply GradedRingHom.ext
  intro x
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk _ (rectangularSubstitution M (rectangularSubstitution N q)) =
    Ideal.Quotient.mk _ q
  rw [← AlgHom.comp_apply, rectangularSubstitution_comp, hNM,
    rectangularSubstitution_one]
  rfl

lemma serreKernelEquationsGraded_inverse_comp
    (A : Matrix (Fin 6) (Fin 9) R) (M : Matrix (Fin 9) (Fin 3) R)
    (N : Matrix (Fin 3) (Fin 9) R) (D : Matrix (Fin 9) (Fin 6) R)
    (hAM : A * M = 0) (hsplit : M * N + D * A = 1) :
    (serreKernelEquationsGradedInverse A N).comp
      (serreKernelEquationsGradedMap A M hAM) = GradedRingHom.id _ := by
  have hq : (Ideal.Quotient.mkₐ R (serreEvaluationEquationIdeal A)).comp
      (rectangularSubstitution (M * N)) = Ideal.Quotient.mkₐ R (serreEvaluationEquationIdeal A) := by
    apply MvPolynomial.algHom_ext
    intro i
    change Ideal.Quotient.mk _ (rectangularSubstitution (M * N) (X i)) =
      Ideal.Quotient.mk _ (X i)
    rw [rectangularSubstitution_X]
    exact serreEvaluationEquationIdeal_quotientCoordinate A M N D hsplit i
  apply GradedRingHom.ext
  intro x
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk _ (rectangularSubstitution N (rectangularSubstitution M q)) =
    Ideal.Quotient.mk _ q
  rw [← AlgHom.comp_apply, rectangularSubstitution_comp]
  exact congrArg (fun f : MvPolynomial (Fin 9) R →ₐ[R]
    (MvPolynomial (Fin 9) R ⧸ serreEvaluationEquationIdeal A) => f q) hq

/-- Literal split evaluation equations define an actual projective plane over
its coordinate ring, without a fibre-dimension certificate. -/
def serreKernelEquationsSchemeIso
    (A : Matrix (Fin 6) (Fin 9) R) (M : Matrix (Fin 9) (Fin 3) R)
    (N : Matrix (Fin 3) (Fin 9) R) (D : Matrix (Fin 9) (Fin 6) R)
    (hAM : A * M = 0) (hNM : N * M = 1) (hsplit : M * N + D * A = 1) :
    scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) R)) ≅
      scheme (serreEvaluationHomogeneousIdeal A) := by
  let F := serreKernelEquationsGradedMap A M hAM
  let G := serreKernelEquationsGradedInverse A N
  have hFG : F.comp G = GradedRingHom.id _ :=
    serreKernelEquationsGraded_comp_inverse A M N hAM hNM
  have hGF : G.comp F = GradedRingHom.id _ :=
    serreKernelEquationsGraded_inverse_comp A M N D hAM hsplit
  have hF : Function.Surjective F := by
    intro y
    refine ⟨G y, ?_⟩
    exact congrArg (fun f => f y) hFG
  have hG : Function.Surjective G := by
    intro x
    refine ⟨F x, ?_⟩
    exact congrArg (fun f => f x) hGF
  let hF' := gradedSurjective_irrelevant_le F hF
  let hG' := gradedSurjective_irrelevant_le G hG
  refine ⟨Proj.map F hF', Proj.map G hG', ?_, ?_⟩
  · change Proj.map F hF' ≫ Proj.map G hG' =
      𝟙 (Proj (grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) R))))
    rw [← Proj.map_comp G F hG' hF']
    simpa only [hFG] using (Proj.map_id (𝒜 := grading
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) R))))
  · change Proj.map G hG' ≫ Proj.map F hF' =
      𝟙 (Proj (grading (serreEvaluationHomogeneousIdeal A)))
    rw [← Proj.map_comp F G hF' hG']
    simpa only [hGF] using (Proj.map_id (𝒜 := grading (serreEvaluationHomogeneousIdeal A)))

end PfaffianDescent
