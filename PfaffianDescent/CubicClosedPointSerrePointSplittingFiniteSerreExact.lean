import PfaffianDescent.CubicClosedPointSerrePointSplittingFiniteSerreOneTensor

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- The native finite-support tensor isomorphism IS the actual point evaluator. -/
theorem pointSplittingFiniteSerreSectionsTensorEquiv_eq_evaluator
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
:
    (pointSplittingFiniteSerreSectionsTensorEquiv base d s C hField e he).toLinearMap =
      cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor
        (d ≫ base)
        (fun k => pointSplittingFiniteComponentPoint (d ≫ base) 3 e (ULift.up k))
        (fun k => pointSplittingFiniteComponentPoint_toBase (d ≫ base) 3 e he (ULift.up k))
        ((Scheme.Modules.pullback d).obj (show X.Modules from s.E)) := by
  let f := (pointSplittingFiniteSerreSectionsTensorEquiv base d s C hField e he).toLinearMap
  let g := cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor
    (d ≫ base)
    (fun k => pointSplittingFiniteComponentPoint (d ≫ base) 3 e (ULift.up k))
    (fun k => pointSplittingFiniteComponentPoint_toBase (d ≫ base) 3 e he (ULift.up k))
    ((Scheme.Modules.pullback d).obj (show X.Modules from s.E))
  change f = g
  apply LinearMap.ext
  intro w
  induction w using TensorProduct.induction_on with
  | zero => exact f.map_zero.trans g.map_zero.symm
  | add x y hx hy => rw [f.map_add, g.map_add, hx, hy]
  | tmul c σ =>
    have hw : c ⊗ₜ[F] σ = c • (1 ⊗ₜ[F] σ) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hw, f.map_smul, g.map_smul]
    apply congrArg (fun v => c • v)
    exact pointSplittingFiniteSerreSectionsTensorEquiv_one_tmul_evaluator base d s C hField e he σ

/-- Actual finite-support tensor point evaluation is bijective, with native
free frame and coefficient comparisons discharged internally. -/
theorem pointSplittingFiniteSerre_actual_tensor_evaluator_bijective
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
:
    Function.Bijective
      (cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor
        (d ≫ base)
        (fun k => pointSplittingFiniteComponentPoint (d ≫ base) 3 e (ULift.up k))
        (fun k => pointSplittingFiniteComponentPoint_toBase (d ≫ base) 3 e he (ULift.up k))
        ((Scheme.Modules.pullback d).obj (show X.Modules from s.E))) := by
  rw [← pointSplittingFiniteSerreSectionsTensorEquiv_eq_evaluator base d s C hField e he]
  exact (pointSplittingFiniteSerreSectionsTensorEquiv base d s C hField e he).bijective

end PfaffianDescent
