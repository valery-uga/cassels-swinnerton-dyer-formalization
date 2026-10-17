import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCubicNativeGroundRankRange
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGroundFrameNativeOpen

/-! # Native cubic unit minors select parameters in the actual unordered kernel frame -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
variable {K E : Type u} [Field K] [Field E]
variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
variable [hB : IsIntegral (cubicConfigurationBase p hp 3)]
local instance : IsIntegral (projectiveConfigurationQuotientOpen
    (grading (equationIdeal p hp)) (toBase (equationIdeal p hp)) 3).toScheme := hB
variable [hordered : IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left]
local instance : IsIntegral (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) 3).left := hordered
variable (c : Spec (.of E) ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left)
variable (β : (cubicConfigurationBase p hp 3).functionField →+* E)
variable (hβ : Spec.map (CommRingCat.ofHom β) ≫
    (cubicConfigurationBase p hp 3).fromSpecStalk
      (genericPoint (cubicConfigurationBase p hp 3)) =
    c ≫ configurationQuotientMap (equationIdeal p hp) 3)
variable (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp 3).functionField)
variable (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 3 ≫
    cubicConfigurationToBase p hp 3)


open ProjectiveNegativeTwist

include β hβ a ha

/-- Surjectivity of the literal native field matrix follows from the actual
unit minor and the original section evaluator; no matrix-rank certificate is
supplied independently. -/
theorem serreIncidenceCubicNativeRank_original_matrix_surjective
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (h9 : Module.finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9)
    {A : Scheme.{u}}
    (aRank : A ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left)
    (chart : Fin 3 → C.ι) (marked : ∀ i, A ⟶ (C.U (chart i)).toScheme)
    (hmarked : ∀ i, marked i ≫ (C.U (chart i)).ι =
      (aRank ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 3)) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) 3 i).left)
    (m : (Fin 3 × ULift.{u} (Fin 2)) ↪ Fin 9)
    (hm : IsUnit (Matrix.det (Matrix.submatrix
      (serreIncidenceNativeAffineEvaluationMatrix (hypersurfaceToBase p hp) e C h9 chart marked) id m)))
    (cA : Spec (.of E) ⟶ A) (hcA : cA ≫ aRank = c)
    (ρ : Fin 6 ≃ (Fin 3 × ULift.{u} (Fin 2))) :
    Function.Surjective (Matrix.toLin'
      (serreIncidenceCubicOriginalNativeMatrix p hp e C h9 chart marked cA ρ)) := by
  letI : Algebra K E := (β.comp a.hom).toAlgebra
  have hpoint : ∀ i, (cA ≫ marked i) ≫ (C.U (chart i)).ι =
      serreIncidenceCubicOriginalMarkedPoint p hp c i := by
    intro i
    rw [Category.assoc, hmarked i]
    simp only [← Category.assoc, hcA]
    rfl
  have hold := pointSplittingCubicSerreNativeRank_original_evaluation_surjective
    p hp c β hβ a ha e C h9 aRank chart marked hmarked m hm cA hcA
  exact serreIncidenceMatrix_surjective_of_actual_tensor_columns_anyIndex (ι := Fin 6)
    (Module.finBasisOfFinrankEq K
      (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) h9)
    (pointSplittingCubicSerrePulledEvaluation_originalEvaluator p hp c β hβ a ha e.E)
    hold
    (serreIncidenceCubicOriginalNativeExactCoordinates p hp c e C chart marked cA hpoint ρ)
    (serreIncidenceCubicOriginalNativeMatrix p hp e C h9 chart marked cA ρ)
    (fun k => serreIncidenceCubicOriginalNativeMatrix_named_column
      p hp c β hβ a ha e C h9 chart marked cA hpoint ρ k)

/-- Every nonempty open of the actual marked kernel contains a parameter
coming from the same native unordered kernel frame. The kernel dimension,
left inverse, range equality, and field-matrix surjectivity are derived from
the original unit minor. -/
theorem serreIncidenceCubicNativeRankOpen_exists_ground_parameter
    [Infinite (cubicConfigurationBase p hp 3).functionField]
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (h9 : Module.finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9)
    {A : Scheme.{u}}
    (aRank : A ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left)
    (chart : Fin 3 → C.ι) (marked : ∀ i, A ⟶ (C.U (chart i)).toScheme)
    (hmarked : ∀ i, marked i ≫ (C.U (chart i)).ι =
      (aRank ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 3)) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) 3 i).left)
    (m : (Fin 3 × ULift.{u} (Fin 2)) ↪ Fin 9)
    (hm : IsUnit (Matrix.det (Matrix.submatrix
      (serreIncidenceNativeAffineEvaluationMatrix (hypersurfaceToBase p hp) e C h9 chart marked) id m)))
    (cA : Spec (.of E) ⟶ A) (hcA : cA ≫ aRank = c)
    (ρ : Fin 6 ≃ (Fin 3 × ULift.{u} (Fin 2)))
    (U : (scheme (serreEvaluationHomogeneousIdeal
      (serreIncidenceCubicOriginalNativeMatrix p hp e C h9 chart marked cA ρ))).Opens)
    (hU : (U : Set (scheme (serreEvaluationHomogeneousIdeal
      (serreIncidenceCubicOriginalNativeMatrix p hp e C h9 chart marked cA ρ)))).Nonempty) :
    let F : Type u := (cubicConfigurationBase p hp 3).functionField
    letI : Algebra F E := β.toAlgebra
    ∃ (h3 : Module.finrank F
      (LinearMap.ker (serreIncidenceCubicNativeGroundRestriction p hp a ha e C)) = 3)
      (H : Matrix (Fin 3) (Fin 9) F)
      (hHG : H * serreIncidenceCubicNativeGroundKernelMatrix p hp a ha e C h9 h3 = 1)
      (qF : Spec (.of F) ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)))
      (qE : Spec (.of E) ⟶ (U : Scheme.{u})),
      qF ≫ toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)) = 𝟙 _ ∧
      qE ≫ U.ι ≫ toBase (serreEvaluationHomogeneousIdeal
        (serreIncidenceCubicOriginalNativeMatrix p hp e C h9 chart marked cA ρ)) = 𝟙 _ ∧
      qE ≫ U.ι ≫ schemeQuotientMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) E))
        (serreEvaluationHomogeneousIdeal
          (serreIncidenceCubicOriginalNativeMatrix p hp e C h9 chart marked cA ρ)) bot_le ≫
        projectiveCoefficientMap (algebraMap F E)
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) F))
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) E)) (by simp) =
        Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ qF ≫
          serreKernelFrameProjectiveEmbedding
            (serreIncidenceCubicNativeGroundKernelMatrix p hp a ha e C h9 h3) H hHG := by
  let F : Type u := (cubicConfigurationBase p hp 3).functionField
  letI : Algebra F E := β.toAlgebra
  dsimp only
  obtain ⟨h3, H, hHG, hrange⟩ := serreIncidenceCubicNativeRank_exists_ground_kernel_range
    p hp c β hβ a ha e C h9 aRank chart marked hmarked m hm cA hcA ρ
  have honto := serreIncidenceCubicNativeRank_original_matrix_surjective
    p hp c β hβ a ha e C h9 aRank chart marked hmarked m hm cA hcA ρ
  obtain ⟨qF, qE, hF, hE, hcoeff⟩ :=
    serreIncidenceGroundFrameNativeOpen_exists_ground_parameter
      (serreIncidenceCubicNativeGroundKernelMatrix p hp a ha e C h9 h3) H hHG
      (serreIncidenceCubicOriginalNativeMatrix p hp e C h9 chart marked cA ρ)
      hrange honto U hU
  exact ⟨h3, H, hHG, qF, qE, hF, hE, hcoeff⟩

end PfaffianDescent
