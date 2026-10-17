import PfaffianDescent.QuarticTwistedCubicQuadraticPiece
import PfaffianDescent.QuarticTwistedCubicGeometricPresentation
import PfaffianDescent.ProjectiveLinearCoordinateSchemeIso

namespace PfaffianDescent.QuarticNet

open MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
open scoped MatrixGroups

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable {K : Type u} [Field K]

/-- Pulling the standard cubic ideal back along an invertible linear coordinate
change yields a quadratically generated ideal with a three-dimensional quadratic piece. -/
theorem coordinateChange_standardTwistedCubic_quadraticPiece
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (hIJ : (standardTwistedCubicHomogeneousIdeal (K := K)).toIdeal =
      I.toIdeal.map (linearSubstitutionEquiv M hM).toRingHom) :
    quadraticPieceGenerates I ∧
      Module.finrank K (homogeneousIdealPiece I 2) = 3 := by
  let E := linearSubstitutionEquiv M hM
  let Q : Fin 3 → MvPolynomial (Fin 4) K := fun i => E.symm (standardTwistedCubicGenerators K i)
  have hback : I.toIdeal = (standardTwistedCubicHomogeneousIdeal (K := K)).toIdeal.map
      (↑E.symm : MvPolynomial (Fin 4) K →+* MvPolynomial (Fin 4) K) := by
    simpa only [E] using linearCoordinateChange_ideal_symm M hM I
      (standardTwistedCubicHomogeneousIdeal (K := K)) hIJ
  have hQ : ∀ i, (Q i).IsHomogeneous 2 := by
    intro i
    exact homogeneous_equiv_symm E (fun _ p hp => linearSubstitution_homogeneous M hp) 2
      (standardTwistedCubicGenerators_homogeneous K i)
  have hIQ : I.toIdeal = Ideal.span (Set.range Q) := by
    calc
      I.toIdeal = (standardTwistedCubicHomogeneousIdeal (K := K)).toIdeal.map
          (↑E.symm : MvPolynomial (Fin 4) K →+* MvPolynomial (Fin 4) K) := hback
      _ = (Ideal.span (Set.range (standardTwistedCubicGenerators K))).map
          (↑E.symm : MvPolynomial (Fin 4) K →+* MvPolynomial (Fin 4) K) := by rfl
      _ = Ideal.span (Set.range Q) := by
        rw [Ideal.map_span]
        congr 1
        ext p
        constructor
        · rintro ⟨q, ⟨i, rfl⟩, rfl⟩
          exact ⟨i, rfl⟩
        · rintro ⟨i, rfl⟩
          exact ⟨standardTwistedCubicGenerators K i, ⟨i, rfl⟩, rfl⟩
  have hlin : LinearIndependent K Q := by
    rw [show Q = (E.symm.toLinearEquiv :
      MvPolynomial (Fin 4) K ≃ₗ[K] MvPolynomial (Fin 4) K) ∘ standardTwistedCubicGenerators K by rfl]
    exact LinearIndependent.map' (standardTwistedCubicGenerators_linearIndependent (K := K))
      E.symm.toLinearEquiv.toLinearMap E.symm.toLinearEquiv.ker
  exact ⟨quadraticPieceGenerates_of_ideal_eq_span_quadrics I Q hQ hIQ,
    finrank_homogeneousIdealPiece_eq_three_of_ideal_eq_span_quadrics I Q hQ hIQ hlin⟩

/-- Any ground-field linear presentation of the standard twisted cubic has
the expected quadratic generators and quadratic-piece dimension. -/
theorem GroundTwistedCubicPresentation.quadraticPiece
    {I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)}
    (hI : GroundTwistedCubicPresentation I) :
    quadraticPieceGenerates I ∧
      Module.finrank K (homogeneousIdealPiece I 2) = 3 := by
  let M : GL (Fin 4) K := Classical.choose hI
  have hM : I.toIdeal.map
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) K)).toRingHom =
      standardTwistedCubicIdeal K := Classical.choose_spec hI
  have hdet : IsUnit ((M : Matrix (Fin 4) (Fin 4) K).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit M)
  have hIJ : (standardTwistedCubicHomogeneousIdeal (K := K)).toIdeal =
      I.toIdeal.map
        (linearSubstitutionEquiv (M : Matrix (Fin 4) (Fin 4) K) hdet).toRingHom := by
    change standardTwistedCubicIdeal K = I.toIdeal.map
      (linearSubstitutionEquiv (M : Matrix (Fin 4) (Fin 4) K) hdet).toRingHom
    exact hM.symm
  exact coordinateChange_standardTwistedCubic_quadraticPiece I
    (M : Matrix (Fin 4) (Fin 4) K) hdet hIJ

end PfaffianDescent.QuarticNet
