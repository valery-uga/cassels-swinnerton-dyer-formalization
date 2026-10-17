import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNormalizedInfinityEndpointIdeal
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNormalizedEndpointKernel
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

theorem cubicClosedPointSerreFiniteZeroResidual_normalizedInfinityEndpoint_kernel
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e) :
    (C.projectiveLineNormalizedLocalPencilZeroGluedToAmbient f seed).ker.comap
      (cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointAmbient f true) =
    (C.localPencilZeroGluedToAmbient e seed 0 (𝟙 _)).ker := by
  let I := (C.projectiveLineNormalizedLocalPencilZeroGluedToAmbient f seed).ker
  let J := (C.localPencilZeroGluedToAmbient e seed 0 (𝟙 _)).ker
  apply cubicClosedPointSerreFiniteZeroResidual_ideal_eq_of_affine_pullbacks
    (I.comap (cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointAmbient f true)) J
    (fun k => ⟨C.U k, C.affine k⟩) C.covers
  intro k
  rw [← Scheme.IdealSheafData.comap_comp,
    cubicClosedPointSerreFiniteZeroResidual_normalizedEndpointAmbient_local,
    Scheme.IdealSheafData.comap_comp]
  have hI := C.projectiveLineNormalizedLocalPencilZeroGluedToAmbient_ker_comap f seed (k, true)
  change I.comap _ = _ at hI
  rw [hI, cubicClosedPointSerreFiniteZeroResidual_normalizedInfinityEndpointChart_ideal,
    cubicClosedPointSerreFiniteZeroResidual_localGlued_kernel_comap]

end
end PfaffianDescent
