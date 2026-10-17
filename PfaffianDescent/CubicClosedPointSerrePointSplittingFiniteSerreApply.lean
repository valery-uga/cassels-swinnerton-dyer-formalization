import PfaffianDescent.CubicClosedPointSerrePointSplittingFiniteSerreEquiv
import PfaffianDescent.CubicClosedPointSerrePointSplittingFiniteSpecSectionApply

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

/-- The finite-support tensor comparison evaluates the SAME actual section at
its actual split components. -/
theorem pointSplittingFiniteSerreSectionsTensorEquiv_one_tmul
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    {X D : Scheme.{u}} [IsAffine D] {M : X.Modules}
    (base : X ⟶ Spec (.of F)) (d : D ⟶ X) [IsFinite (d ≫ base)]
    (s : SerreExtensionData X M)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover s)
    (hField : IsField Γ(D, ⊤))
    (e : (∐ fun _ : ULift.{u} (Fin 3) ↦ Spec (.of E)) ≅
      pullback (d ≫ base) (Spec.map (CommRingCat.ofHom (algebraMap F E))))
    (he : e.hom ≫ pullback.snd (d ≫ base)
        (Spec.map (CommRingCat.ofHom (algebraMap F E))) =
      AllCharacteristics.constantCoverToBase (ULift.{u} (Fin 3)) (Spec (.of E)))
    (σ : SchemeModuleGlobalSectionsOver (d ≫ base)
      ((Scheme.Modules.pullback d).obj (show X.Modules from s.E))) (k : Fin 3) :
    pointSplittingFiniteSerreSectionsTensorEquiv base d s C hField e he (1 ⊗ₜ[F] σ) k =
      (pullbackSection (pointSplittingFiniteComponentPoint (d ≫ base) 3 e (ULift.up k))
        ((Scheme.Modules.pullback d).obj (show X.Modules from s.E))
        (isIso_pullbackUnitComparison _)
        (((Scheme.Modules.pullback d).obj (show X.Modules from s.E)).unitHomEquiv σ)).val (op ⊤) := by
  let q := d ≫ base
  letI := finiteSchemeCoefficientAlgebra q
  letI : Field Γ(D, ⊤) := hField.toField
  let N := (Scheme.Modules.pullback d).obj (show X.Modules from s.E)
  let NA := (Scheme.Modules.pullback D.isoSpec.inv).obj N
  let t := Classical.choice (pointSplittingFiniteSerreSpec_exists_freeIso s C d hField)
  let α := fun k : Fin 3 => pointSplittingFiniteComponentAlgHom q 3 e he (ULift.up k)
  let ρ := pointSplittingFiniteTripleCoefficientEquiv q e he
  let A := pointSplittingFiniteSpecSectionsEquiv base d (show X.Modules from s.E)
  have hρ : ∀ a : Γ(D, ⊤), ρ (1 ⊗ₜ[F] a) = fun k => α k a := by
    intro a
    exact pointSplittingFiniteTripleCoefficientEquiv_one_tmul q e he a
  dsimp only [pointSplittingFiniteSerreSectionsTensorEquiv, LinearEquiv.trans_apply]
  rw [LinearEquiv.baseChange_tmul]
  rw [pointSplittingSectionTensorEquiv_one_tmul _ _ _ _ _ hρ]
  rw [cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor_one_tmul]
  change ((moduleSpecΓFunctor (R := CommRingCat.of E)).map
      (pointSplittingFiniteSpecPointModuleIso
        (Spec.map (CommRingCat.ofHom (α k).toRingHom))
        (pointSplittingFiniteComponentPoint q 3 e (ULift.up k))
        (pointSplittingFiniteComponentAlgHom_spec q 3 e he (ULift.up k)) N).hom).hom
    ((pullbackSection (Spec.map (CommRingCat.ofHom (α k).toRingHom)) NA
      (isIso_pullbackUnitComparison _) (NA.unitHomEquiv (A σ))).val (op ⊤)) = _
  rw [pointSplittingFiniteSpecSectionsEquiv_section]
  exact congrArg (fun v => v.val (op ⊤))
    (pointSplittingFiniteSpecPointModuleIso_section
      (Spec.map (CommRingCat.ofHom (α k).toRingHom))
      (pointSplittingFiniteComponentPoint q 3 e (ULift.up k))
      (pointSplittingFiniteComponentAlgHom_spec q 3 e he (ULift.up k)) N (N.unitHomEquiv σ))

end PfaffianDescent
