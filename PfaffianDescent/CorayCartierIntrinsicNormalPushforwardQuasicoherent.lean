import PfaffianDescent.SchemeModuleRankOneHomCokernelFinitePresentation
import PfaffianDescent.CorayCartierIntrinsicNormalHomSequence

/-! Native quasicoherence of the actual Cartier coefficient on the source
AND its SAME ambient pushforward. The ambient proof uses the genuine OWN
residue cokernel and canonical intrinsic-normal comparison, rather than
assuming pushforward quasicoherence or a comparison certificate.
SOURCE ONLY / UNVERIFIED. Root owns compiler and acceptance checks. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- The actual adjunction candidate and its actual ambient pushforward are
quasicoherent, internally from OWN regular geometry and original W charts. -/
theorem RegularPrincipalImmersion.actualIntrinsicNormalCoefficient_and_pushforward_isQuasicoherent
    {X Z : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i]
    (H : RegularPrincipalImmersion i) (W : X.Modules)
    (hW : schemeModuleLocallyRankOne W) :
    (schemeModuleTensor ((Scheme.Modules.pullback i).obj W)
      (SchemeModuleInternalHom.dual (actualClosedImmersionConormalModule i))).IsQuasicoherent ∧
    ((Scheme.Modules.pushforward i).obj
      (schemeModuleTensor ((Scheme.Modules.pullback i).obj W)
        (SchemeModuleInternalHom.dual (actualClosedImmersionConormalModule i)))).IsQuasicoherent := by
  let I := IdealSheafDataModule.closedImmersionModule i
  let T := schemeModuleTensor W (SchemeModuleInternalHom.dual I)
  let D := schemeModuleTensor ((Scheme.Modules.pullback i).obj W)
    (SchemeModuleInternalHom.dual (actualClosedImmersionConormalModule i))
  let P := (Scheme.Modules.pushforward i).obj D
  have hD : schemeModuleLocallyRankOne D :=
    schemeModuleLocallyRankOne_tensor _ _
      (schemeModuleLocallyRankOne_pullback i W hW) H.actualNormal_locallyRankOne
  have hFree : D.IsLocallyFree := schemeModuleLocallyRankOne_isLocallyFree D hD
  obtain ⟨q, hq⟩ := hFree.exists_isLocallyFreeData
  letI : q.IsLocallyFreeData := hq
  have hDQC : D.IsQuasicoherent := q.quasiCoherentData.isQuasicoherent
  have hT : schemeModuleLocallyRankOne T := schemeModuleLocallyRankOne_tensor W _ hW
    (schemeModuleLocallyRankOne_dual I H.inverseCartierTwist_locallyRankOne)
  let delta := schemeModuleRankOneTensorDualIncrement
    (IdealSheafDataModule.closedImmersionModuleToUnit i) W
  let A := H.actualCartierResidueSequence W
  let hA := H.actualCartierResidueSequence_shortExact W hW
  letI : (cokernel delta).IsQuasicoherent :=
    schemeModuleRankOneHom_cokernel_isQuasicoherent W T hW hT delta
  let eC : cokernel delta ≅ A.X₃ :=
    CokernelCofork.mapIsoOfIsColimit (cokernelIsCokernel delta) hA.gIsCokernel
      (Iso.refl (Arrow.mk delta))
  let e : cokernel delta ≅ P := eC ≪≫ H.actualCartierResidueIntrinsicNormalTensorIso W hW
  have hP : P.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e inferInstance
  exact ⟨hDQC, hP⟩

end PfaffianDescent
end
