import PfaffianDescent.CubicClosedPointSerrePointSplittingFiniteSerreExact
import PfaffianDescent.CubicClosedPointSerrePointSplittingRestrictionTensor
import PfaffianDescent.CubicClosedPointSerrePointSplittingKernelTransport
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- Actual split evaluation onto descends to actual finite-scheme restriction;
all finite-support comparison and frame hypotheses are discharged internally. -/
theorem pointSplittingFiniteSerre_restriction_surjective
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
    (hglobal : Function.Surjective
      (cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor
        base
        (fun k => pointSplittingFiniteComponentPoint (d ≫ base) 3 e (ULift.up k) ≫ d)
        (fun k => by simpa only [Category.assoc] using
          pointSplittingFiniteComponentPoint_toBase (d ≫ base) 3 e he (ULift.up k))
        (show X.Modules from s.E))) :
    Function.Surjective
      (cubicClosedPointSerreDegreeThreeEvaluationMap base d (show X.Modules from s.E)) := by
  exact pointSplitting_actual_restriction_surjective_of_split base d
    (fun k => pointSplittingFiniteComponentPoint (d ≫ base) 3 e (ULift.up k))
    (fun k => pointSplittingFiniteComponentPoint_toBase (d ≫ base) 3 e he (ULift.up k))
    (show X.Modules from s.E)
    (pointSplittingFiniteSerre_actual_tensor_evaluator_bijective base d s C hField e he)
    hglobal

/-- The original restriction kernel after scalar extension is identified
with the actual ordered point-evaluation kernel, without changing its vectors. -/
def pointSplittingFiniteSerre_restriction_kernel_tensor_equiv
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
    (E ⊗[F] LinearMap.ker
      (cubicClosedPointSerreDegreeThreeEvaluationMap base d (show X.Modules from s.E))) ≃ₗ[E]
    LinearMap.ker
      (cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor
        base
        (fun k => pointSplittingFiniteComponentPoint (d ≫ base) 3 e (ULift.up k) ≫ d)
        (fun k => by simpa only [Category.assoc] using
          pointSplittingFiniteComponentPoint_toBase (d ≫ base) 3 e he (ULift.up k))
        (show X.Modules from s.E)) := by
  let δ := fun k : Fin 3 => pointSplittingFiniteComponentPoint (d ≫ base) 3 e (ULift.up k)
  let hδ := fun k => pointSplittingFiniteComponentPoint_toBase (d ≫ base) 3 e he (ULift.up k)
  let N := show X.Modules from s.E
  let R := cubicClosedPointSerreDegreeThreeEvaluationMap base d N
  let T := cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor
    base (fun k => δ k ≫ d) (fun k => by simpa only [Category.assoc] using hδ k) N
  let A := pointSplittingFiniteSerreSectionsTensorEquiv base d s C hField e he
  let B := pointSplittingRestrictionTripleFiberEquiv d δ N
  have h : A.toLinearMap.comp (R.baseChange E) = B.toLinearMap.comp T := by
    rw [pointSplittingFiniteSerreSectionsTensorEquiv_eq_evaluator]
    exact pointSplitting_restriction_tensor_square base d δ hδ N
  exact pointSplittingKernelTensorEquiv R ≪≫ₗ
    pointSplittingKernelEquivOfSquare (R.baseChange E) T A B h

end PfaffianDescent
