import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNormalizedEndpointIdeal
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNormalizedEndpointAmbient
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualIdealCover

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

theorem cubicClosedPointSerreFiniteZeroResidual_localGlued_kernel_comap
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (C.localPencilZeroGluedToAmbient e seed a b).ker.comap (C.U i).ι =
      C.localPencilZeroIdeal e seed i a b := by
  let c := C.localPencilZeroGluedToAmbient e seed a b
  letI : IsClosedImmersion c :=
    C.isClosedImmersion_localPencilZeroGluedToAmbient_of_localPencilZeroGluing e seed a b
  rw [← cubicClosedPointSerreFiniteZeroResidual_pullback_snd_kernel]
  let v := C.localPencilZeroGluedTargetPullbackι e seed i a b
  letI : IsIso v := C.isIso_localPencilZeroGluedTargetPullbackι e seed i a b
    (C.range_localPencilZeroGluedTargetPullbackι_eq_univ e seed i a b)
  rw [← Scheme.Hom.ker_comp_of_isIso v (pullback.snd c (C.U i).ι),
    C.localPencilZeroGluedTargetPullbackι_comp_snd e seed i a b,
    Scheme.IdealSheafData.ker_subschemeι]

theorem cubicClosedPointSerreFiniteZeroResidual_normalizedEndpoint_kernel
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e) :
    (C.projectiveLineNormalizedLocalPencilZeroGluedToAmbient f seed).ker.comap
      (cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointAmbient f false) =
    (C.localPencilZeroGluedToAmbient e seed (𝟙 _) 0).ker := by
  let I := (C.projectiveLineNormalizedLocalPencilZeroGluedToAmbient f seed).ker
  let J := (C.localPencilZeroGluedToAmbient e seed (𝟙 _) 0).ker
  apply cubicClosedPointSerreFiniteZeroResidual_ideal_eq_of_affine_pullbacks
    (I.comap (cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointAmbient f false)) J
    (fun k => ⟨C.U k, C.affine k⟩) C.covers
  intro k
  rw [← Scheme.IdealSheafData.comap_comp,
    cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointAmbient_local,
    Scheme.IdealSheafData.comap_comp]
  have hI := C.projectiveLineNormalizedLocalPencilZeroGluedToAmbient_ker_comap f seed (k, false)
  change I.comap _ = _ at hI
  rw [hI, cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointChart_ideal,
    cubicClosedPointSerreFiniteZeroResidual_localGlued_kernel_comap]

end
end PfaffianDescent
