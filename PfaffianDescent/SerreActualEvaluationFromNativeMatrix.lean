import PfaffianDescent.SerreTensorEvaluationFromMatrix
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNativeTensorMatrix

/-! The actual native unit minor gives actual tensor evaluation onto at
every actual field-valued point of the SAME chart. -/
noncomputable section
open AlgebraicGeometry CategoryTheory Module
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreActualEvaluation_surjective_of_native_matrix
    {K E : Type u} [Field K] [Field E] [Algebra K E]
    {X B : Scheme.{u}} {N : X.Modules}
    (base : X ⟶ Spec (.of K)) (e : SerreExtensionData X N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))]
    (h9 : finrank K (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E)) = 9)
    (chart : Fin 3 → C.ι) (marked : ∀ i, B ⟶ (C.U (chart i)).toScheme)
    (c : Spec (.of E) ⟶ B) (r : Fin 3 → (Spec (.of E) ⟶ X))
    (hpoint : ∀ i, (c ≫ marked i) ≫ (C.U (chart i)).ι = r i)
    (hr : ∀ i, r i ≫ base = Spec.map (CommRingCat.ofHom (algebraMap K E)))
    (hM : Function.Surjective (Matrix.toLin'
      ((serreIncidenceNativeAffineEvaluationMatrix base e C h9 chart marked).map
        (fieldPointΓevaluation c)))) :
    Function.Surjective
      (cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor
        base r hr (show X.Modules from e.E)) := by
  exact serreIncidence_actual_tensor_surjective_of_matrix_columns
    (Module.finBasisOfFinrankEq K (SchemeModuleGlobalSectionsOver base
      (show X.Modules from e.E)) h9)
    (cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor
      base r hr (show X.Modules from e.E))
    (serreIncidenceThreePointCoordinateEquiv (show X.Modules from e.E)
      (ULift.{u} (Fin 2)) (serreIncidenceRankTwoAffineCover e C) chart
      (fun i => c ≫ marked i) r hpoint)
    ((serreIncidenceNativeAffineEvaluationMatrix base e C h9 chart marked).map
      (fieldPointΓevaluation c))
    (fun k => serreIncidenceNativeTensorMatrix_column base e C h9 chart marked c r hpoint hr k) hM

theorem serreActualEvaluation_surjective_of_native_unit_minor
    {K E : Type u} [Field K] [Field E] [Algebra K E]
    {X B : Scheme.{u}} {N : X.Modules}
    (base : X ⟶ Spec (.of K)) (e : SerreExtensionData X N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))]
    (h9 : finrank K (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E)) = 9)
    (chart : Fin 3 → C.ι) (marked : ∀ i, B ⟶ (C.U (chart i)).toScheme)
    (m : (Fin 3 × ULift.{u} (Fin 2)) ↪ Fin 9)
    (hm : IsUnit (Matrix.det (Matrix.submatrix
      (serreIncidenceNativeAffineEvaluationMatrix base e C h9 chart marked) id m)))
    (c : Spec (.of E) ⟶ B) (r : Fin 3 → (Spec (.of E) ⟶ X))
    (hpoint : ∀ i, (c ≫ marked i) ≫ (C.U (chart i)).ι = r i)
    (hr : ∀ i, r i ≫ base = Spec.map (CommRingCat.ofHom (algebraMap K E))) :
    Function.Surjective
      (cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor
        base r hr (show X.Modules from e.E)) := by
  let f := fieldPointΓevaluation c
  have hmE := hm.map f
  rw [RingHom.map_det] at hmE
  change IsUnit (Matrix.det (Matrix.submatrix
    ((serreIncidenceNativeAffineEvaluationMatrix base e C h9 chart marked).map f) id m)) at hmE
  exact serreActualEvaluation_surjective_of_native_matrix base e C h9 chart marked c r hpoint hr
    (serreIncidenceMatrix_surjective_of_unit_minor
      ((serreIncidenceNativeAffineEvaluationMatrix base e C h9 chart marked).map f) m hmE)

end PfaffianDescent
