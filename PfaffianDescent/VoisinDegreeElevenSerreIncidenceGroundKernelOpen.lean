import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGroundKernelAmbient
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGroundFrameCoefficientSquare
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceProjectiveGroundOpen

/-! # Actual kernel-incidence opens contain parameters from the ground kernel frame -/
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceGroundKernelOpen_exists_ground_parameter
    {K E : Type u} [Field K] [Field E] [Algebra K E] [Infinite K]
    (M : Matrix (Fin 9) (Fin 3) K) (N : Matrix (Fin 3) (Fin 9) K)
    (hNM : N * M = 1) (A : Matrix (Fin 6) (Fin 9) E)
    (D : Matrix (Fin 9) (Fin 6) E)
    (hAM : A * M.map (algebraMap K E) = 0)
    (hsplit : M.map (algebraMap K E) * N.map (algebraMap K E) + D * A = 1)
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
  let e := serreKernelEquationsSchemeIso A (M.map (algebraMap K E))
    (N.map (algebraMap K E)) D hAM
    (serreIncidenceGroundFrame_map_leftInverse (algebraMap K E) M N hNM) hsplit
  let V := e.hom ⁻¹ᵁ U
  have hV : (V : Set (scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) E)))).Nonempty := by
    obtain ⟨x, hx⟩ := hU
    refine ⟨e.inv x, ?_⟩
    change e.hom (e.inv x) ∈ U
    rw [← Scheme.Hom.comp_apply, e.inv_hom_id]
    exact hx
  obtain ⟨qK, q, hK, hE, hcoeff⟩ :=
    serreIncidenceProjectiveOpen_exists_ground_parameter (K := K) V hV
  let qE := q ≫ e.hom ∣_ U
  have hinc : qE ≫ U.ι = q ≫ V.ι ≫ e.hom := by
    simp only [qE, V, Category.assoc, morphismRestrict_ι]
  have hebase : e.hom ≫ toBase (serreEvaluationHomogeneousIdeal A) =
      toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) E)) :=
    serreKernelEquationsSchemeIso_hom_toBase A _ _ D hAM _ hsplit
  have heambient : e.hom ≫ schemeQuotientMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) E))
      (serreEvaluationHomogeneousIdeal A) bot_le =
      serreKernelFrameProjectiveEmbedding (M.map (algebraMap K E))
        (N.map (algebraMap K E))
        (serreIncidenceGroundFrame_map_leftInverse (algebraMap K E) M N hNM) :=
    serreIncidenceGroundKernelSchemeIso_toAmbient A _ _ D hAM _ hsplit
  refine ⟨qK, qE, hK, ?_, ?_⟩
  · have hc := congrArg (fun z => z ≫ toBase (serreEvaluationHomogeneousIdeal A)) hinc
    simp only [Category.assoc, hebase] at hc
    exact hc.trans hE
  · let z := schemeQuotientMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) E))
      (serreEvaluationHomogeneousIdeal A) bot_le
    let c := projectiveCoefficientMap (algebraMap K E)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K))
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) E)) (by simp)
    have hc := congrArg (fun t => t ≫ z ≫ c) hinc
    have hec := congrArg (fun t => t ≫ c) heambient
    simp only [Category.assoc] at hec hc
    rw [hec, serreIncidenceGroundFrame_coefficient_square (algebraMap K E) M N hNM] at hc
    have hfinal := congrArg (fun t => t ≫ serreKernelFrameProjectiveEmbedding M N hNM) hcoeff
    simp only [Category.assoc] at hfinal
    exact hc.trans hfinal

end PfaffianDescent
