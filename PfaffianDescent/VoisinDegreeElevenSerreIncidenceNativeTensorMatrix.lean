import PfaffianDescent.VoisinDegreeElevenSerreIncidenceThreePointCoordinates
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceTensorMatrixSurjective

/-! # The surjective actual tensor evaluator gives the literal native chart matrix rank -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite Module
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceNativeTensorMatrix_column
    {K E : Type u} [Field K] [Field E] [Algebra K E] {X B : Scheme.{u}} {N : X.Modules}
    (base : X ⟶ Spec (.of K)) (e : SerreExtensionData X N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))]
    (h9 : Module.finrank K (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E)) = 9)
    (chart : Fin 3 → C.ι) (marked : ∀ i, B ⟶ (C.U (chart i)).toScheme)
    (c : Spec (.of E) ⟶ B) (r : Fin 3 → (Spec (.of E) ⟶ X))
    (hpoint : ∀ i, (c ≫ marked i) ≫ (C.U (chart i)).ι = r i)
    (hr : ∀ i, r i ≫ base = Spec.map (CommRingCat.ofHom (algebraMap K E))) (k : Fin 9) :
    serreIncidenceThreePointCoordinateEquiv (show X.Modules from e.E)
      (ULift.{u} (Fin 2)) (serreIncidenceRankTwoAffineCover e C) chart
      (fun i => c ≫ marked i) r hpoint
      (cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor base r hr
        (show X.Modules from e.E) (1 ⊗ₜ[K]
          Module.finBasisOfFinrankEq K (SchemeModuleGlobalSectionsOver base
            (show X.Modules from e.E)) h9 k)) =
    ((serreIncidenceNativeAffineEvaluationMatrix base e C h9 chart marked).map
      (fieldPointΓevaluation c)).col k := by
  funext a
  rw [serreIncidenceThreePointCoordinateEquiv_tensor_section]
  exact (serreIncidenceNativeAffineEvaluationMatrix_fieldPoint
    base e C h9 chart marked c a k).symm

theorem serreIncidenceNativeAffineEvaluationMatrix_surjective_of_actual_tensor_evaluation
    {K E : Type u} [Field K] [Field E] [Algebra K E] {X B : Scheme.{u}} {N : X.Modules}
    (base : X ⟶ Spec (.of K)) (e : SerreExtensionData X N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))]
    (h9 : Module.finrank K (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E)) = 9)
    (chart : Fin 3 → C.ι) (marked : ∀ i, B ⟶ (C.U (chart i)).toScheme)
    (c : Spec (.of E) ⟶ B) (r : Fin 3 → (Spec (.of E) ⟶ X))
    (hpoint : ∀ i, (c ≫ marked i) ≫ (C.U (chart i)).ι = r i)
    (hr : ∀ i, r i ≫ base = Spec.map (CommRingCat.ofHom (algebraMap K E)))
    (honto : Function.Surjective
      (cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor base r hr
        (show X.Modules from e.E))) :
    Function.Surjective (Matrix.toLin'
      ((serreIncidenceNativeAffineEvaluationMatrix base e C h9 chart marked).map
        (fieldPointΓevaluation c))) := by
  exact serreIncidenceMatrix_surjective_of_actual_tensor_columns
    (Module.finBasisOfFinrankEq K (SchemeModuleGlobalSectionsOver base
      (show X.Modules from e.E)) h9)
    (cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor base r hr
      (show X.Modules from e.E)) honto
    (serreIncidenceThreePointCoordinateEquiv (show X.Modules from e.E)
      (ULift.{u} (Fin 2)) (serreIncidenceRankTwoAffineCover e C) chart
      (fun i => c ≫ marked i) r hpoint)
    ((serreIncidenceNativeAffineEvaluationMatrix base e C h9 chart marked).map
      (fieldPointΓevaluation c))
    (fun k => serreIncidenceNativeTensorMatrix_column base e C h9 chart marked c r hpoint hr k)

end PfaffianDescent
