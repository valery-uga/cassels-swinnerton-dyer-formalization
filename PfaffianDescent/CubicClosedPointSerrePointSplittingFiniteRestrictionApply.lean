import PfaffianDescent.CubicClosedPointSerrePointSplittingFiniteRestriction
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual unordered restriction-kernel comparison retains literal
scalar-extended global section coefficients. -/
theorem pointSplittingFiniteSerre_restriction_kernel_tensor_equiv_tmul
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
    (c : E) (σ : LinearMap.ker
      (cubicClosedPointSerreDegreeThreeEvaluationMap base d (show X.Modules from s.E))) :
    (pointSplittingFiniteSerre_restriction_kernel_tensor_equiv base d s C hField e he
      (c ⊗ₜ[F] σ) : E ⊗[F] SchemeModuleGlobalSectionsOver base (show X.Modules from s.E)) =
      c ⊗ₜ[F] (σ : SchemeModuleGlobalSectionsOver base (show X.Modules from s.E)) := by
  simp only [pointSplittingFiniteSerre_restriction_kernel_tensor_equiv,
    LinearEquiv.trans_apply, pointSplittingKernelEquivOfSquare_coe,
    pointSplittingKernelTensorEquiv_tmul]

end PfaffianDescent
