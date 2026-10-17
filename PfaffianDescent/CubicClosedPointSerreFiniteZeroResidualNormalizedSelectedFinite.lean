import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNormalizedInfinityEndpointIso
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualFieldPointFinitePullback
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualGoodOpen

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
open SerreExtensionData
universe u
set_option backward.isDefEq.respectTransparency false
section
variable {K : Type u} [Field K] {X : Scheme.{u}}
  {M : SheafOfModules.{u} X.ringCatSheaf} {e : SerreExtensionData X M}
  (f : X ⟶ Spec (.of K)) [IsProper f]

theorem cubicClosedPointSerreFiniteZeroResidual_normalizedSelected_finite
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (hf : ((C.projectiveLineNormalizedLocalPencilZeroGluedToAmbient f seed ≫
      projectiveLineAmbientToLine K f) ⁻¹'
        {projectiveLineEndpoint K true (IsLocalRing.closedPoint K)}).Finite) :
    IsFinite (C.localPencilZeroGluedToAmbient e seed 0 (𝟙 _) ≫ f) := by
  let i := C.projectiveLineNormalizedLocalPencilZeroGluedToAmbient f seed
  let ep := cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointAmbient f true
  let g := i ≫ projectiveLineAmbientToLine K f
  let s := projectiveLineEndpoint K true
  letI : Mono s := mono_of_mono_fac (f := projectiveLineProjToBase K) (g := s)
    (projectiveLineEndpoint_toBase K true)
  letI : Finite ↥(pullback g s) :=
    cubicClosedPointSerreFiniteZeroResidual_fieldPoint_pullback_finite g s hf
  have h : IsPullback (pullback.fst i ep) (pullback.snd i ep ≫ f) g s :=
    (IsPullback.of_hasPullback i ep).paste_vert
      (cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointAmbient_isPullback f true)
  letI : Finite ↥(pullback i ep) := Finite.of_injective
    (fun x : ↥(pullback i ep) => h.isoPullback.hom x) h.isoPullback.hom.injective
  let a := cubicClosedPointSerreFiniteZeroResidual_normalizedInfinityEndpoint_iso f C seed
  letI : Finite ↥(C.localPencilZeroGluedScheme e seed 0 (𝟙 _)) :=
    Finite.of_injective (fun x : ↥(C.localPencilZeroGluedScheme e seed 0 (𝟙 _)) => a.inv x)
      a.inv.injective
  let c := C.localPencilZeroGluedToAmbient e seed 0 (𝟙 _)
  letI : IsClosedImmersion c :=
    C.isClosedImmersion_localPencilZeroGluedToAmbient_of_localPencilZeroGluing e seed 0 (𝟙 _)
  letI : LocallyQuasiFinite (c ≫ f) :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ (fun _ => Set.toFinite _)
  exact IsFinite.of_isProper_of_locallyQuasiFinite (c ≫ f)

end
end PfaffianDescent
