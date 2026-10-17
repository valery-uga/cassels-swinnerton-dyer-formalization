import PfaffianDescent.CubicClosedPointSerrePointSplittingSectionTensorEquiv

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

variable {F A E : Type u} [Field F] [Field A] [Field E] [Algebra F A] [Algebra F E]
variable (α : Fin 3 → (A →ₐ[F] E)) (I : Type u) [Fintype I] [DecidableEq I]
variable (M : (Spec (.of A)).Modules)
variable (e : SheafOfModules.free (R := (Spec (.of A)).ringCatSheaf) I ≅ M)
variable (ρ : (E ⊗[F] A) ≃ₗ[E] (Fin 3 → E))

theorem pointSplittingSectionTensorEquiv_one_tmul_coord
    (s : SchemeModuleGlobalSectionsOver
      (Spec.map (CommRingCat.ofHom (algebraMap F A))) M) (k : Fin 3) (i : I) :
    pointSplittingNativeSpecSectionCoordinates (E := E) I
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (α k).toRingHom))).obj M)
      (pullbackFreeIso (Spec.map (CommRingCat.ofHom (α k).toRingHom)) I e)
      (pointSplittingSectionTensorEquiv α I M e ρ (1 ⊗ₜ[F] s) k) i =
    ρ (1 ⊗ₜ[F] pointSplittingSpecSectionCoordinates (F := F) I M e s i) k := by
  simp [pointSplittingSectionTensorEquiv, pointSplittingPiTranspose,
    tensorFinitePiLinearEquivOfFamily_tmul_apply]

theorem pointSplittingSectionTensorEquiv_one_tmul
    (hρ : ∀ a : A, ρ (1 ⊗ₜ[F] a) = fun k => α k a)
    (s : SchemeModuleGlobalSectionsOver
      (Spec.map (CommRingCat.ofHom (algebraMap F A))) M) :
    pointSplittingSectionTensorEquiv α I M e ρ (1 ⊗ₜ[F] s) =
    cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor
      (Spec.map (CommRingCat.ofHom (algebraMap F A)))
      (fun k => Spec.map (CommRingCat.ofHom (α k).toRingHom))
      (fun k => pointSplitting_specPoint_over (α k)) M (1 ⊗ₜ[F] s) := by
  apply (LinearEquiv.piCongrRight (fun k : Fin 3 => pointSplittingNativeSpecSectionCoordinates (E := E) I
    ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (α k).toRingHom))).obj M)
    (pullbackFreeIso (Spec.map (CommRingCat.ofHom (α k).toRingHom)) I e))).injective
  funext k i
  change pointSplittingNativeSpecSectionCoordinates (E := E) I _ _
      (pointSplittingSectionTensorEquiv α I M e ρ (1 ⊗ₜ[F] s) k) i = _
  rw [pointSplittingSectionTensorEquiv_one_tmul_coord]
  rw [hρ, cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor_one_tmul]
  change _ = pointSplittingNativeSpecSectionCoordinates (E := E) I
    ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (α k).toRingHom))).obj M)
    (pullbackFreeIso (Spec.map (CommRingCat.ofHom (α k).toRingHom)) I e)
    ((pullbackSection (Spec.map (CommRingCat.ofHom (α k).toRingHom)) M
      (isIso_pullbackUnitComparison _) (M.unitHomEquiv s)).val (op ⊤)) i
  rw [← cubicClosedPointSerreSurfaceJetCotangent_pointSectionEvaluation_apply
    (Spec.map (CommRingCat.ofHom (algebraMap F A))) _ (pointSplitting_specPoint_over (α k))]
  exact (pointSplitting_component_evaluation_coordinate (α k) I M e s i).symm

end PfaffianDescent
