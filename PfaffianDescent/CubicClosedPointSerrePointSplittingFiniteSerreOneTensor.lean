import PfaffianDescent.CubicClosedPointSerrePointSplittingFiniteSerreApply
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem pointSplittingFiniteSerreSectionsTensorEquiv_one_tmul_evaluator
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
      ((Scheme.Modules.pullback d).obj (show X.Modules from s.E))) :
    pointSplittingFiniteSerreSectionsTensorEquiv base d s C hField e he (1 ⊗ₜ[F] σ) =
      cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor
        (d ≫ base)
        (fun k => pointSplittingFiniteComponentPoint (d ≫ base) 3 e (ULift.up k))
        (fun k => pointSplittingFiniteComponentPoint_toBase (d ≫ base) 3 e he (ULift.up k))
        ((Scheme.Modules.pullback d).obj (show X.Modules from s.E)) (1 ⊗ₜ[F] σ) := by
  rw [cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor_one_tmul]
  funext k
  exact pointSplittingFiniteSerreSectionsTensorEquiv_one_tmul base d s C hField e he σ k

end PfaffianDescent
