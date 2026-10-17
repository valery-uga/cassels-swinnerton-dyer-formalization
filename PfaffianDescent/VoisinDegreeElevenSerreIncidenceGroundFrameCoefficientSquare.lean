import PfaffianDescent.VoisinDegreeElevenSerreIncidenceKernelProjectiveEmbedding
import AllCharacteristics.ProjectiveCoefficientMap

/-! # The actual kernel-frame projective embedding commutes with coefficients -/
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

lemma serreIncidenceGroundFrame_map_leftInverse
    {K E : Type u} [CommRing K] [CommRing E] (g : K →+* E)
    (M : Matrix (Fin 9) (Fin 3) K) (N : Matrix (Fin 3) (Fin 9) K)
    (hNM : N * M = 1) : N.map g * M.map g = 1 := by
  rw [← Matrix.map_mul, hNM]
  exact Matrix.map_one g (map_zero g) (map_one g)

theorem serreIncidenceGroundFrame_coefficient_square
    {K E : Type u} [CommRing K] [CommRing E] (g : K →+* E)
    (M : Matrix (Fin 9) (Fin 3) K) (N : Matrix (Fin 3) (Fin 9) K)
    (hNM : N * M = 1) :
    serreKernelFrameProjectiveEmbedding (M.map g) (N.map g)
        (serreIncidenceGroundFrame_map_leftInverse g M N hNM) ≫
      projectiveCoefficientMap g
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K))
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) E)) (by simp) =
    projectiveCoefficientMap g
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) K))
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) E)) (by simp) ≫
      serreKernelFrameProjectiveEmbedding M N hNM := by
  unfold serreKernelFrameProjectiveEmbedding polynomialProjectiveMap projectiveCoefficientMap
  rw [← Proj.map_comp, ← Proj.map_comp]
  congr 1
  apply GradedRingHom.ext
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk _ (rectangularSubstitution (M.map g) (MvPolynomial.map g p)) =
    Ideal.Quotient.mk _ (MvPolynomial.map g (rectangularSubstitution M p))
  apply congrArg (Ideal.Quotient.mk _)
  exact (congrArg (fun f : MvPolynomial (Fin 9) K →+*
    MvPolynomial (Fin 3) E => f p) (rectangularSubstitution_map_comm g M)).symm

end PfaffianDescent
