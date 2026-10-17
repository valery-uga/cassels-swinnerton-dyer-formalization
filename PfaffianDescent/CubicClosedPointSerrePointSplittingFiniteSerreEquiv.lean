import PfaffianDescent.CubicClosedPointSerrePointSplittingTripleCoefficients
import PfaffianDescent.CubicClosedPointSerrePointSplittingFiniteSpecPoint
import PfaffianDescent.CubicClosedPointSerrePointSplittingSectionTensorExact

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual finite-scheme section space after scalar extension is the
product of the actual three point fibers. The canonical Spec presentation,
coefficient algebra split and rank-two free frame are constructed internally. -/
def pointSplittingFiniteSerreSectionsTensorEquiv
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
      AllCharacteristics.constantCoverToBase (ULift.{u} (Fin 3)) (Spec (.of E))) :
    (E ⊗[F] SchemeModuleGlobalSectionsOver (d ≫ base)
      ((Scheme.Modules.pullback d).obj (show X.Modules from s.E))) ≃ₗ[E]
    (∀ k : Fin 3, (moduleSpecΓFunctor (R := CommRingCat.of E)).obj
      ((Scheme.Modules.pullback
        (pointSplittingFiniteComponentPoint (d ≫ base) 3 e (ULift.up k))).obj
        ((Scheme.Modules.pullback d).obj (show X.Modules from s.E)))) := by
  let q := d ≫ base
  letI := finiteSchemeCoefficientAlgebra q
  letI : Field Γ(D, ⊤) := hField.toField
  let N := (Scheme.Modules.pullback d).obj (show X.Modules from s.E)
  let NA := (Scheme.Modules.pullback D.isoSpec.inv).obj N
  let t := Classical.choice (pointSplittingFiniteSerreSpec_exists_freeIso s C d hField)
  let α := fun k : Fin 3 => pointSplittingFiniteComponentAlgHom q 3 e he (ULift.up k)
  let ρ := pointSplittingFiniteTripleCoefficientEquiv q e he
  let A := pointSplittingFiniteSpecSectionsEquiv base d (show X.Modules from s.E)
  let B := pointSplittingSectionTensorEquiv α (ULift.{u} (Fin 2)) NA t ρ
  let V := LinearEquiv.piCongrRight (fun k : Fin 3 =>
    ((moduleSpecΓFunctor (R := CommRingCat.of E)).mapIso
      (pointSplittingFiniteSpecPointModuleIso
        (Spec.map (CommRingCat.ofHom (α k).toRingHom))
        (pointSplittingFiniteComponentPoint q 3 e (ULift.up k))
        (pointSplittingFiniteComponentAlgHom_spec q 3 e he (ULift.up k)) N)).toLinearEquiv)
  exact A.baseChange F E _ _ ≪≫ₗ B ≪≫ₗ V

end PfaffianDescent
