import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNormalizedInfinityEndpointKernel
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNormalizedEndpointPullback

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
open SerreExtensionData
universe u
set_option backward.isDefEq.respectTransparency false
section
variable {K : Type u} [Field K] {X : Scheme.{u}}
  {M : SheafOfModules.{u} X.ringCatSheaf} {e : SerreExtensionData X M}
  (f : X ⟶ Spec (.of K)) [IsSeparated f]

private theorem infinityEndpointPullback_kernel
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e) :
    (pullback.snd (C.projectiveLineNormalizedLocalPencilZeroGluedToAmbient f seed)
      (cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointAmbient f true)).ker =
    (C.localPencilZeroGluedToAmbient e seed 0 (𝟙 _)).ker := by
  letI := C.isClosedImmersion_projectiveLineNormalizedLocalPencilZeroGluedToAmbient f seed
  rw [cubicClosedPointSerreFiniteZeroResidual_pullback_snd_kernel]
  exact cubicClosedPointSerreFiniteZeroResidual_normalizedInfinityEndpoint_kernel f C seed

def cubicClosedPointSerreFiniteZeroResidual_normalizedInfinityEndpoint_iso
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e) :
    pullback (C.projectiveLineNormalizedLocalPencilZeroGluedToAmbient f seed)
      (cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointAmbient f true) ≅
    C.localPencilZeroGluedScheme e seed 0 (𝟙 _) := by
  let i := C.projectiveLineNormalizedLocalPencilZeroGluedToAmbient f seed
  let ep := cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointAmbient f true
  let j := pullback.snd i ep
  let c := C.localPencilZeroGluedToAmbient e seed 0 (𝟙 _)
  letI : IsClosedImmersion i := C.isClosedImmersion_projectiveLineNormalizedLocalPencilZeroGluedToAmbient f seed
  letI : IsClosedImmersion c :=
    C.isClosedImmersion_localPencilZeroGluedToAmbient_of_localPencilZeroGluing e seed 0 (𝟙 _)
  exact asIso j.toImage ≪≫
    eqToIso (congrArg Scheme.IdealSheafData.subscheme (infinityEndpointPullback_kernel f C seed)) ≪≫
    (asIso c.toImage).symm

theorem cubicClosedPointSerreFiniteZeroResidual_normalizedInfinityEndpoint_iso_over
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e) :
    (cubicClosedPointSerreFiniteZeroResidual_normalizedInfinityEndpoint_iso f C seed).hom ≫
      C.localPencilZeroGluedToAmbient e seed 0 (𝟙 _) =
    pullback.snd (C.projectiveLineNormalizedLocalPencilZeroGluedToAmbient f seed)
      (cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointAmbient f true) := by
  let i := C.projectiveLineNormalizedLocalPencilZeroGluedToAmbient f seed
  let ep := cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointAmbient f true
  let j := pullback.snd i ep
  let c := C.localPencilZeroGluedToAmbient e seed 0 (𝟙 _)
  letI : IsClosedImmersion i := C.isClosedImmersion_projectiveLineNormalizedLocalPencilZeroGluedToAmbient f seed
  letI : IsClosedImmersion c :=
    C.isClosedImmersion_localPencilZeroGluedToAmbient_of_localPencilZeroGluing e seed 0 (𝟙 _)
  have hc : (asIso c.toImage).inv ≫ c = c.imageι := by
    calc
      (asIso c.toImage).inv ≫ c =
          (asIso c.toImage).inv ≫ (c.toImage ≫ c.imageι) :=
        congrArg (fun a : C.localPencilZeroGluedScheme e seed 0 (𝟙 _) ⟶ X =>
          (asIso c.toImage).inv ≫ a) c.toImage_imageι.symm
      _ = c.imageι := (asIso c.toImage).inv_hom_id_assoc c.imageι
  change ((asIso j.toImage).hom ≫
      (eqToIso (congrArg Scheme.IdealSheafData.subscheme (infinityEndpointPullback_kernel f C seed))).hom ≫
      (asIso c.toImage).inv) ≫ c = j
  rw [Category.assoc, Category.assoc, hc]
  exact (congrArg (fun a => (asIso j.toImage).hom ≫ a)
    (idealSheafData_eqToIso_subschemeι j.ker c.ker (infinityEndpointPullback_kernel f C seed))).trans
    j.toImage_imageι

end
end PfaffianDescent
