import PfaffianDescent.CubicClosedPointSerreLocalFreeAlgebra
import PfaffianDescent.CubicClosedPointSerreLocalFreeCoordinate

/-! # Rank-two freeness of the actual Serre extension at its original point

No geometric extension or Galois orbit is needed. The actual globally
nonzero connecting product has nonzero actual stalk. Its local ideal
sequence and the actual extension are normalized using constructed stalk
isomorphisms; their Yoneda product forces the relation coefficient to be a
unit in the original local ring.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra


/-- Every actual positive-three Serre extension with nonzero connecting
product has a free rank-two stalk at the original closed field point. The
local presentation and connecting-class comparison are proved internally. -/
theorem cubicClosedPointSerreLocalFree_stalk_rank_two
    (K : Type u) [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hSmooth : Smooth (hypersurfaceToBase p hp)] {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [hClosed : IsClosedImmersion i]
    [hExt : HasExt.{u} (hypersurface p hp).Modules]
    [hExtStalk : HasExt.{u + 1}
      (ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (i default)))]
    (e : SerreExtensionSequenceData (hypersurface p hp)
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)))
    (hne :
      letI := quotientPositiveTwist_tensorRight_preservesFiniteLimits (equationIdeal p hp) 3
      letI := quotientPositiveTwist_tensorRight_preservesFiniteColimits (equationIdeal p hp) 3
      (closedImmersionIdealTwistSequence_shortExact i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)).extClass.comp
        (@SerreExtensionSequenceData.extensionClass.{u} (hypersurface p hp) _ e hExt)
        (show 1 + 1 = 2 by omega) ≠ 0) :
    letI : Module ((hypersurface p hp).presheaf.stalk (i default))
      ((show (hypersurface p hp).Modules from e.E).presheaf.stalk (i default)) :=
      schemeModuleStalkModule (show (hypersurface p hp).Modules from e.E) (i default)
    Nonempty (((show (hypersurface p hp).Modules from e.E).presheaf.stalk (i default)) ≃ₗ[
      (hypersurface p hp).presheaf.stalk (i default)]
      ((hypersurface p hp).presheaf.stalk (i default)) ×
        ((hypersurface p hp).presheaf.stalk (i default))) := by
  let X := hypersurface p hp
  letI : HasExt.{u} X.Modules := hExt
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExt
  let R := X.presheaf.stalk (i default)
  letI : HasExt.{u + 1} (ModuleCat.{u} R) := hExtStalk
  let F : X.Modules ⥤ ModuleCat.{u} R := schemeModuleStalkModuleFunctor X (i default)
  letI : F.Additive := by dsimp [F]; infer_instance
  letI : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive F
  letI : PreservesFiniteLimits F := by dsimp [F]; infer_instance
  letI : PreservesFiniteColimits F := by dsimp [F]; infer_instance
  let P := positiveSheafOfModules (grading (equationIdeal p hp)) 3
  letI : PreservesFiniteLimits (schemeModuleTensorRight P) :=
    quotientPositiveTwist_tensorRight_preservesFiniteLimits (equationIdeal p hp) 3
  letI : PreservesFiniteColimits (schemeModuleTensorRight P) :=
    quotientPositiveTwist_tensorRight_preservesFiniteColimits (equationIdeal p hp) 3
  let T : ShortComplex (ModuleCat.{u} R) := (closedImmersionIdealTwistSequence i P).map F
  let S : ShortComplex (ModuleCat.{u} R) := e.complex.map F
  let hT : T.ShortExact := (closedImmersionIdealTwistSequence_shortExact i P).map_of_exact F
  let hS : S.ShortExact := e.shortExact.map_of_exact F
  let d := cubicPointCompatibleResiduePresentation K p hp hp0 i
  have hspan : Ideal.span ({d.f, d.g} : Set R) = IsLocalRing.maximalIdeal R :=
    d.span_eq_maximalIdeal_of_unit_source i default _ _
  let q₂ : T.X₂ ≅ ModuleCat.of R R :=
    F.mapIso (closedImmersionIdealTwistSequence_middleIso i P) ≪≫
      cubicClosedPointSerreLocalFree_positiveTwistStalkIso K p hp i
  let q₃ : T.X₃ ≅ ModuleCat.of R (R ⧸ Ideal.span ({d.f, d.g} : Set R)) :=
    cubicClosedPointSerreLocalFree_positivePointStalkIso K p hp i d.f d.g hspan
  let qN : S.X₁ ≅ ModuleCat.of R R := schemeModuleUnitStalkIso X (i default)
  have hlocal : hT.extClass.comp hS.extClass (show 1 + 1 = 2 by omega) ≠ 0 := by
    have h := cubicClosedPointSerreLocalFree_positive_stalk_ne_zero K p hp hp0 i
      ((closedImmersionIdealTwistSequence_shortExact i P).extClass.comp
        (@SerreExtensionSequenceData.extensionClass.{u} (hypersurface p hp) _ e hExt)
        (show 1 + 1 = 2 by omega)) hne
    change ((closedImmersionIdealTwistSequence_shortExact i P).extClass.comp
      e.shortExact.extClass (show 1 + 1 = 2 by omega)).mapExactFunctor F ≠ 0 at h
    rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass,
      Ext.mapExactFunctor_extClass] at h
    exact h
  exact cubicClosedPointSerreLocalFree_of_nonzero_yoneda T hT S.X₁ S.X₂ S.f S.g S.zero hS
    d.f d.g d.hf d.hg hspan q₂ q₃ qN hlocal

/-- The preceding explicit rank-two equivalence gives literal module
freeness of the actual middle sheaf's stalk. -/
theorem cubicClosedPointSerreLocalFree_stalk_free
    (K : Type u) [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hSmooth : Smooth (hypersurfaceToBase p hp)] {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [hClosed : IsClosedImmersion i]
    [hExt : HasExt.{u} (hypersurface p hp).Modules]
    [hExtStalk : HasExt.{u + 1}
      (ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (i default)))]
    (e : SerreExtensionSequenceData (hypersurface p hp)
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)))
    (hne :
      letI := quotientPositiveTwist_tensorRight_preservesFiniteLimits (equationIdeal p hp) 3
      letI := quotientPositiveTwist_tensorRight_preservesFiniteColimits (equationIdeal p hp) 3
      (closedImmersionIdealTwistSequence_shortExact i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)).extClass.comp
        (@SerreExtensionSequenceData.extensionClass.{u} (hypersurface p hp) _ e hExt)
        (show 1 + 1 = 2 by omega) ≠ 0) :
    letI : Module ((hypersurface p hp).presheaf.stalk (i default))
      ((show (hypersurface p hp).Modules from e.E).presheaf.stalk (i default)) :=
      schemeModuleStalkModule (show (hypersurface p hp).Modules from e.E) (i default)
    Module.Free ((hypersurface p hp).presheaf.stalk (i default))
      ((show (hypersurface p hp).Modules from e.E).presheaf.stalk (i default)) := by
  letI := schemeModuleStalkModule (show (hypersurface p hp).Modules from e.E) (i default)
  let R := (hypersurface p hp).presheaf.stalk (i default)
  letI : Module.Free R (R × R) := Module.Free.prod R R R
  obtain ⟨q⟩ := cubicClosedPointSerreLocalFree_stalk_rank_two K p hp hp0 i e hne
  exact Module.Free.of_equiv q.symm

end PfaffianDescent.ProjectiveNegativeTwist
