import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGroundKernelOpen
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGroundFrameNativeSplit

/-! # Native evaluation and the literal ground kernel frame select a ground parameter -/
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceGroundFrameNativeOpen_exists_ground_parameter
    {K E : Type u} [Field K] [Field E] [Algebra K E] [Infinite K]
    (M : Matrix (Fin 9) (Fin 3) K) (N : Matrix (Fin 3) (Fin 9) K)
    (hNM : N * M = 1) (A : Matrix (Fin 6) (Fin 9) E)
    (hrange : LinearMap.range (Matrix.toLin' (M.map (algebraMap K E))) =
      LinearMap.ker (Matrix.toLin' A))
    (honto : Function.Surjective (Matrix.toLin' A))
    (U : (scheme (serreEvaluationHomogeneousIdeal A)).Opens)
    (hU : (U : Set (scheme (serreEvaluationHomogeneousIdeal A))).Nonempty) :
    ∃ (qK : Spec (.of K) ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) K)))
      (qE : Spec (.of E) ⟶ (U : Scheme.{u})),
      qK ≫ toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) K)) = 𝟙 _ ∧
      qE ≫ U.ι ≫ toBase (serreEvaluationHomogeneousIdeal A) = 𝟙 _ ∧
      qE ≫ U.ι ≫
        schemeQuotientMap (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) E))
          (serreEvaluationHomogeneousIdeal A) bot_le ≫
        projectiveCoefficientMap (algebraMap K E)
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K))
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) E)) (by simp) =
      Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫ qK ≫
        serreKernelFrameProjectiveEmbedding M N hNM := by
  obtain ⟨D, hAM, hsplit⟩ := serreIncidenceGroundFrame_native_split M N hNM A hrange honto
  exact serreIncidenceGroundKernelOpen_exists_ground_parameter M N hNM A D hAM hsplit U hU

end PfaffianDescent
