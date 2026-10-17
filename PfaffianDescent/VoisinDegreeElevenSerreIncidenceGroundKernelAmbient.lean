import PfaffianDescent.VoisinDegreeElevenSerreIncidenceKernelSchemeProjection

/-! # The actual split-kernel plane retains its section-coordinate embedding -/
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceGroundKernelSchemeIso_toAmbient
    {R : Type u} [CommRing R]
    (A : Matrix (Fin 6) (Fin 9) R) (M : Matrix (Fin 9) (Fin 3) R)
    (N : Matrix (Fin 3) (Fin 9) R) (D : Matrix (Fin 9) (Fin 6) R)
    (hAM : A * M = 0) (hNM : N * M = 1) (hsplit : M * N + D * A = 1) :
    (serreKernelEquationsSchemeIso A M N D hAM hNM hsplit).hom ≫
      schemeQuotientMap (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) R))
        (serreEvaluationHomogeneousIdeal A) bot_le =
      serreKernelFrameProjectiveEmbedding M N hNM := by
  change Proj.map (serreKernelEquationsGradedMap A M hAM) _ ≫
      Proj.map (gradedQuotientMap _ _ bot_le) _ =
    Proj.map (polynomialQuotientGradingMap _ _ (rectangularSubstitution M) bot_le
      (fun _ _ hp => rectangularSubstitution_homogeneous M hp)) _
  rw [← Proj.map_comp]
  congr 1
  apply GradedRingHom.ext
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

end PfaffianDescent
