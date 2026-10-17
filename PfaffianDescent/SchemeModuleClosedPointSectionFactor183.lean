import PfaffianDescent.SchemeModuleClosedPointFiberZero182

/-! The SAME original section factors through the SAME point-ideal tensor
inclusion. Fiber zero and kernel exactness are constructed internally.
SOURCE ONLY / UNVERIFIED, including source182 dependency. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open IdealSheafDataModule
universe u
variable {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Support in the original whole cokernel internally gives the point
fiber zero and then the actual kernel factor; no factor/exactness premise. -/
theorem schemeModuleUnitHom_closedPoint_exists_idealTensor_factor183
    (M : X.Modules) (hM : schemeModuleLocallyRankOne M)
    (φ : SheafOfModules.unit X.ringCatSheaf ⟶ M) (P : closedPoints X)
    (hP : P.1 ∈ Coray.schemeModuleStalkSupport (cokernel φ)) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∃ v : SheafOfModules.unit X.ringCatSheaf ⟶
        schemeModuleTensor (show X.Modules from closedImmersionModule i) M,
      v ≫ (schemeModuleTensorMap (closedImmersionModuleToUnit i) (𝟙 M) ≫
        (schemeModuleTensorUnitLeftIso M).hom) = φ := by
  classical
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let beta := schemeModuleTensorMap (closedImmersionModuleToUnit i) (𝟙 M) ≫
    (schemeModuleTensorUnitLeftIso M).hom
  let eta := (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M
  obtain ⟨hz, hS, _⟩ :=
    schemeModuleLocallyRankOne_closedPoint_idealTensor_fiberSequence P M hM
  have hz' : beta ≫ eta = 0 := hz
  let S := ShortComplex.mk beta eta hz'
  have hS' : S.ShortExact := hS
  letI : Mono S.f := hS'.mono_f
  have hphi : φ ≫ S.g = 0 :=
    schemeModuleUnitHom_closedPoint_fiber_zero_of_cokernel_support182 M hM φ P hP
  exact hS'.exact.lift' φ hphi

/-- Exact section specialization; the original M and original s are retained. -/
theorem schemeModuleTopSectionHom_closedPoint_exists_idealTensor_factor183
    (M : X.Modules) (hM : schemeModuleLocallyRankOne M)
    (s : M.val.obj (op ⊤)) (P : closedPoints X)
    (hP : P.1 ∈ Coray.schemeModuleStalkSupport (cokernel (schemeModuleTopSectionHom M s))) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    ∃ v : SheafOfModules.unit X.ringCatSheaf ⟶
        schemeModuleTensor (show X.Modules from closedImmersionModule i) M,
      v ≫ (schemeModuleTensorMap (closedImmersionModuleToUnit i) (𝟙 M) ≫
        (schemeModuleTensorUnitLeftIso M).hom) = schemeModuleTopSectionHom M s :=
  schemeModuleUnitHom_closedPoint_exists_idealTensor_factor183 M hM
    (schemeModuleTopSectionHom M s) P hP

end PfaffianDescent
