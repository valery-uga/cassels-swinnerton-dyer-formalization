import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualLocalYonedaNonzero
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualCoverStalkFree
import PfaffianDescent.CubicClosedPointSerreLocalFree
noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
open SerreExtensionData BundleSectionZeroLocus
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
theorem cubicClosedPointSerreFiniteZeroResidual_yoneda_nonzero_of_rankTwoCover
    (K : Type u) [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hSmooth : Smooth (hypersurfaceToBase p hp)] {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [hClosed : IsClosedImmersion i]
    [hExt : HasExt.{u} (hypersurface p hp).Modules]
    [hExtStalk : HasExt.{u + 1}
      (ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (i default)))]
    (e : SerreExtensionData (hypersurface p hp)
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)))
    (C : SerreExtensionRankTwoAffineCover e) :
      letI := quotientPositiveTwist_tensorRight_preservesFiniteLimits (equationIdeal p hp) 3
      letI := quotientPositiveTwist_tensorRight_preservesFiniteColimits (equationIdeal p hp) 3
      (closedImmersionIdealTwistSequence_shortExact i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)).extClass.comp
        (@SerreExtensionSequenceData.extensionClass.{u} (hypersurface p hp) _ e.toSequenceData hExt)
        (show 1 + 1 = 2 by omega) ≠ 0 := by
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
  letI : Module.Free R S.X₂ :=
    cubicClosedPointSerreFiniteZeroResidual_rankTwoCover_stalk_free e C (i default)
  have hlocal := cubicClosedPointSerreLocalFree_yoneda_nonzero_of_free
    T hT S.X₁ S.X₂ S.f S.g S.zero hS d.f d.g d.hf d.hg hspan q₂ q₃ qN
  intro hz
  apply hlocal
  change (closedImmersionIdealTwistSequence_shortExact i P).extClass.comp
    e.shortExact.extClass (show 1 + 1 = 2 by omega) = 0 at hz
  have hm := congrArg (fun z => z.mapExactFunctor F) hz
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass,
    Ext.mapExactFunctor_extClass, Ext.mapExactFunctor_zero] at hm
  exact hm

end PfaffianDescent.ProjectiveNegativeTwist
