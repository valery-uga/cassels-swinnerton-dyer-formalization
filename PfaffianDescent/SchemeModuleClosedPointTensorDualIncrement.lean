import PfaffianDescent.SchemeModuleRankOneDualKernelAction
import PfaffianDescent.SchemeModuleClosedPointRankOneFiberSequence

/-! The intrinsic point increment for the SAME dual, tensored with an
actual rank-one L. Kernel/evaluation and first-map identities are internally
constructed; the final projection is the SAME actual adjunction unit.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}}

/-- Genuine intrinsic tensor point increment, with the SAME original
inclusion j, dual D, tensor(delta) and adjunction-unit projection. Generic
rank-one geometry is ordinary actual local triviality, not an outcome input. -/
theorem schemeModuleClosedPointTensorDualIncrement_canonical_fiberSequence
    (P : closedPoints X) (L : X.Modules)
    (hM : let i := X.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      schemeModuleLocallyRankOne (closedImmersionModule i))
    (hL : schemeModuleLocallyRankOne L) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from closedImmersionModule i)
    let j := closedImmersionModuleToUnit i
    let T := schemeModuleTensor L (SchemeModuleInternalHom.dual M)
    let deltaL := schemeModuleRankOneTensorDualIncrement j L
    let eta := (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app T
    ∃ hzero : deltaL ≫ eta = 0,
      (ShortComplex.mk deltaL eta hzero).ShortExact ∧
      ∃ E : cokernel deltaL ≅ (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj T),
        cokernel.π deltaL ≫ E.hom = eta ∧
        ∀ F : cokernel deltaL ⟶ (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj T),
          cokernel.π deltaL ≫ F = eta → F = E.hom := by
  classical
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show X.Modules from closedImmersionModule i)
  let j := closedImmersionModuleToUnit i
  let D := SchemeModuleInternalHom.dual M
  let T := schemeModuleTensor L D
  let deltaL := schemeModuleRankOneTensorDualIncrement j L
  let eta := (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app T
  let beta := schemeModuleTensorMap j (𝟙 T) ≫ (schemeModuleTensorUnitLeftIso T).hom
  have hM' : schemeModuleLocallyRankOne M := hM
  have hT : schemeModuleLocallyRankOne T :=
    schemeModuleLocallyRankOne_tensor L D hL (schemeModuleLocallyRankOne_dual M hM')
  obtain ⟨hbeta, hS, _oldCokernel⟩ :=
    schemeModuleLocallyRankOne_closedPoint_idealTensor_fiberSequence P T hT
  have hbetaLocal : beta ≫ eta = 0 := hbeta
  let S := ShortComplex.mk beta eta hbeta
  let eK := schemeModuleRankOneDualKernelIso M L hM'
  have haction : eK.hom ≫ deltaL = beta := schemeModuleRankOneDualKernelIso_action j L hM'
  have hzero : deltaL ≫ eta = 0 := by
    apply (cancel_epi eK.hom).mp
    rw [← Category.assoc, haction, comp_zero]
    exact hbetaLocal
  let A := ShortComplex.mk deltaL eta hzero
  let e : S ≅ A := ShortComplex.isoMk eK (Iso.refl T) (Iso.refl _)
    (by simpa only [S, A, Iso.refl_hom, Category.comp_id] using haction)
    (by simp only [S, A, Iso.refl_hom, Category.id_comp, Category.comp_id])
  have hA : A.ShortExact := ShortComplex.shortExact_of_iso e hS
  let E : cokernel deltaL ≅ (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj T) :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel A.f) hA.gIsCokernel
  have hE : cokernel.π deltaL ≫ E.hom = eta :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (cokernelIsCokernel A.f) hA.gIsCokernel WalkingParallelPair.one
  refine ⟨hzero, hA, E, hE, ?_⟩
  intro F hF
  exact (cancel_epi (cokernel.π deltaL)).mp (hF.trans hE.symm)

end PfaffianDescent
