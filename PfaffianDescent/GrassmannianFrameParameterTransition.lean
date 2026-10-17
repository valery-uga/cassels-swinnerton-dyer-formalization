import PfaffianDescent.GrassmannianProjectiveFrameTransition
import PfaffianDescent.GrassmannianFrameNaturality
import PfaffianDescent.RelativeProjectiveLinearSystem
import PfaffianDescent.RelativeProjectiveBaseChange

/-!
# Compatibility of Grassmannian frame transitions with equation parameters

Changing projective coordinates between two frames and then embedding the
second frame's linear system into the ambient equation space gives the same
morphism as embedding the first frame directly.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

variable {R : Type u} [CommRing R] {τ : Type} [Finite τ] (d : ℕ)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A projective frame transition preserves the represented ambient
homogeneous equation. -/
theorem grassmannianChartHomogeneousFrameProjectiveTransition_toParameters
    {m n : ℕ} (e : Fin (m + n) ≃ Monomials τ d)
    (ρ ρ' : Equiv.Perm (Fin m ⊕ Fin n))
    (T T' : Matrix (Fin n) (Fin m) R)
    (h : grassmannianChartSubmodule R ρ T = grassmannianChartSubmodule R ρ' T') :
    grassmannianChartHomogeneousFrameProjectiveTransition
        (R := R) d e ρ ρ' T T' h ≫
      grassmannianChartHomogeneousFrameToParameters (R := R) d e ρ' T' =
    grassmannianChartHomogeneousFrameToParameters (R := R) d e ρ T := by
  unfold grassmannianChartHomogeneousFrameProjectiveTransition
    grassmannianChartHomogeneousFrameToParameters
    relativeProjectiveLinearSystemMatrixToParameters
    relativeProjectiveLinearSystemToParameters
    projectiveFrameCoordinateMap polynomialProjectiveMap
  change Proj.map _ _ ≫ Proj.map _ _ = Proj.map _ _
  rw [← Proj.map_comp]
  congr 1
  apply GradedRingHom.ext
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [GradedRingHom.comp_apply, polynomialQuotientGradingMap_mk]
  apply congrArg (Ideal.Quotient.mk _)
  unfold relativeProjectiveLinearSystemMatrixSubstitution
  rw [← AlgHom.comp_apply, ← AlgHom.comp_assoc, rectangularSubstitution_comp,
    grassmannianChartHomogeneousFrameCoefficientMatrix_mul_transition
      d e ρ ρ' T T' h]

/-- Embedding a Grassmannian frame into the ambient equation space commutes
with arbitrary extension of the coefficient ring. -/
theorem grassmannianChartHomogeneousFrameToParameters_naturality
    {S : Type u} [CommRing S] (f : R →+* S)
    {m n : ℕ} (e : Fin (m + n) ≃ Monomials τ d)
    (ρ : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) R) :
    projectiveFrameCoordinateCoefficientMap (m := m) f ≫
      grassmannianChartHomogeneousFrameToParameters (R := R) d e ρ T =
    grassmannianChartHomogeneousFrameToParameters
        (R := S) d e ρ (T.map f) ≫
      projectiveParametersCoefficientMap d f := by
  unfold projectiveFrameCoordinateCoefficientMap projectiveCoefficientMap
    grassmannianChartHomogeneousFrameToParameters
    relativeProjectiveLinearSystemMatrixToParameters
    relativeProjectiveLinearSystemToParameters
    projectiveParametersCoefficientMap polynomialProjectiveMap
  change Proj.map _ _ ≫ Proj.map _ _ = Proj.map _ _ ≫ Proj.map _ _
  rw [← Proj.map_comp, ← Proj.map_comp]
  congr 1
  apply GradedRingHom.ext
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [GradedRingHom.comp_apply, polynomialQuotientGradingMap_mk]
  apply congrArg (Ideal.Quotient.mk _)
  unfold relativeProjectiveLinearSystemMatrixSubstitution
  change MvPolynomial.map f
      (rectangularSubstitution
        (grassmannianChartHomogeneousFrameCoefficientMatrix (R := R) d e ρ T)
        (MvPolynomial.rename e.symm p)) =
    rectangularSubstitution
      (grassmannianChartHomogeneousFrameCoefficientMatrix
        (R := S) d e ρ (T.map f))
      (MvPolynomial.rename e.symm (MvPolynomial.map f p))
  rw [← grassmannianChartHomogeneousFrameCoefficientMatrix_baseChange
      (R := R) d f e ρ T,
    ← MvPolynomial.map_rename]
  exact DFunLike.congr_fun
    (rectangularSubstitution_map_comm f
      (grassmannianChartHomogeneousFrameCoefficientMatrix (R := R) d e ρ T))
    (MvPolynomial.rename e.symm p)

/-- The chart-frame morphism to an equation parameter space over an earlier
coefficient ring is functorial under a further coefficient extension. -/
theorem grassmannianChartHomogeneousFrameToGlobalParameters_naturality
    {K S : Type u} [CommRing K] [CommRing S]
    (b : K →+* R) (f : R →+* S)
    {m n : ℕ} (e : Fin (m + n) ≃ Monomials τ d)
    (ρ : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) R) :
    projectiveFrameCoordinateCoefficientMap (m := m) f ≫
      grassmannianChartHomogeneousFrameToGlobalParameters d b e ρ T =
    grassmannianChartHomogeneousFrameToGlobalParameters
      d (f.comp b) e ρ (T.map f) := by
  unfold grassmannianChartHomogeneousFrameToGlobalParameters
  calc
    projectiveFrameCoordinateCoefficientMap (m := m) f ≫
        (grassmannianChartHomogeneousFrameToParameters (R := R) d e ρ T ≫
          projectiveParametersCoefficientMap d b) =
      (projectiveFrameCoordinateCoefficientMap (m := m) f ≫
        grassmannianChartHomogeneousFrameToParameters (R := R) d e ρ T) ≫
          projectiveParametersCoefficientMap d b := (Category.assoc _ _ _).symm
    _ = (grassmannianChartHomogeneousFrameToParameters
        (R := S) d e ρ (T.map f) ≫ projectiveParametersCoefficientMap d f) ≫
          projectiveParametersCoefficientMap d b :=
      congrArg (fun q => q ≫ projectiveParametersCoefficientMap d b)
        (grassmannianChartHomogeneousFrameToParameters_naturality
          (R := R) d f e ρ T)
    _ = grassmannianChartHomogeneousFrameToParameters
        (R := S) d e ρ (T.map f) ≫
          (projectiveParametersCoefficientMap d f ≫
            projectiveParametersCoefficientMap d b) := Category.assoc _ _ _
    _ = grassmannianChartHomogeneousFrameToParameters
        (R := S) d e ρ (T.map f) ≫
          projectiveParametersCoefficientMap d (f.comp b) := by
      rw [projectiveParametersCoefficientMap_comp]

end PfaffianDescent
