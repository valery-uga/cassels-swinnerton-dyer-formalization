import PfaffianDescent.ActualMatchingQuadraticLineProjectiveIso
import AllCharacteristics.ProjectivePoints

/-! SOURCE ONLY, UNVERIFIED. The SAME derived E-frame gives an actual
E-point of the actual E-line, without a supplied point or comparison square. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open Module MvPolynomial AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
variable {E : Type u} [Field E]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem matchingProjectorLineIdeal_le_firstBasisCoordinateKernel
    (C : Basis (Fin 4) E (Fin 4 → E)) :
    (projectorLineIdeal (matchingEdgeProjectorMatrix C)).toIdeal ≤
      RingHom.ker (MvPolynomial.eval₂Hom (algebraMap E E) (C 0)) := by
  classical
  have hP : (matchingEdgeProjectorMatrix C).mulVec (C 0) = C 0 := by
    simpa using matchingEdgeProjectorMatrix_mulVec_basis C 0
  have hN : (1 - matchingEdgeProjectorMatrix C).mulVec (C 0) = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hP, sub_self]
  apply Ideal.span_le.mpr
  rintro q ⟨m, rfl⟩
  change aeval (C 0) (linearCoordinate (1 - matchingEdgeProjectorMatrix C) m) = 0
  rw [linearCoordinate_eval]
  exact congrFun hN m

theorem matchingProjectorLine_has_actual_firstBasisPoint
    (C : Basis (Fin 4) E (Fin 4 → E)) :
    ∃ q : Spec (.of E) ⟶ scheme (projectorLineIdeal (matchingEdgeProjectorMatrix C)),
      q ≫ toBase (projectorLineIdeal (matchingEdgeProjectorMatrix C)) = 𝟙 _ := by
  have hC0 : C 0 ≠ 0 := C.linearIndependent.ne_zero 0
  obtain ⟨q, hq⟩ := point_of_coordinates
    (projectorLineIdeal (matchingEdgeProjectorMatrix C)) (algebraMap E E) (C 0) hC0
    (fun f hf => matchingProjectorLineIdeal_le_firstBasisCoordinateKernel C hf)
  refine ⟨q, ?_⟩
  simpa using hq

end PfaffianDescent.QuarticNet
