import PfaffianDescent.VoisinProjectiveChartPullbackCoordinates
import PfaffianDescent.VoisinFieldBaseChangeOpenPullbackPointEvaluation
import PfaffianDescent.VoisinFieldBaseChangeCoordinateLinearMap

/-!
# Compatibility of geometric and ground basis evaluations

This identifies the geometric field-base-change evaluator on each pulled-back
ground basis section with the exact surface-chart basis value consumed by the
fixed-linear-system descent endpoint.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory BundleSectionZeroLocus

universe u

noncomputable section

/-- The canonical geometric coordinate evaluator agrees on a pulled-back
ground basis section with the surface-open evaluation used by the descent
endpoint. -/
theorem SchemeModuleFiniteFreeAffineCover.fieldBaseChangeOpenPointCoordinateEvaluation_basis_eq_surface
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    (r : Spec (.of L) ⟶
      (C.projectiveSectionOpenCover base M).X ij)
    (hx : (r ≫ C.projectiveSectionOpenCoverToSurfaceChart base M ij) ≫
      ((C.U ij.1).ι ≫ base) =
      Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (a : I)
    (k : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    let U := C.U ij.1
    let xU := r ≫ C.projectiveSectionOpenCoverToSurfaceChart base M ij
    let g := schemeFieldBaseChangeToOriginal (L := L) base
    let V := g ⁻¹ᵁ U
    let ML := (Scheme.Modules.pullback g).obj M
    let pL := schemeFieldBaseChangeToField (L := L) base
    letI : IsAffine (U : Scheme.{u}) := C.affine ij.1
    let qV := moduleRestrictTopLinearEquivOpenSectionsOver pL ML V
    let σ := schemeModuleGlobalSectionsOverEquivSections base M
      (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) k)
    let sV := qV (schemeModuleSectionsEquivTop (ML.restrict V.ι)
      (restrictModuleSection V.ι ML
        (pullbackSection g M (isIso_pullbackUnitComparison g) σ)))
    fieldBaseChangeOpenPointCoordinateEvaluation base M U I
        (C.trivialization ij.1) xU hx a sV =
      C.projectiveSectionSurfaceBasisCoordinateEvaluation base M ij r a k := by
  dsimp only
  let U := C.U ij.1
  let xU := r ≫ C.projectiveSectionOpenCoverToSurfaceChart base M ij
  let g := schemeFieldBaseChangeToOriginal (L := L) base
  let V := g ⁻¹ᵁ U
  let ML := (Scheme.Modules.pullback g).obj M
  let pL := schemeFieldBaseChangeToField (L := L) base
  letI : IsAffine (U : Scheme.{u}) := C.affine ij.1
  let qV := moduleRestrictTopLinearEquivOpenSectionsOver pL ML V
  let σ := schemeModuleGlobalSectionsOverEquivSections base M
    (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) k)
  let sV := qV (schemeModuleSectionsEquivTop (ML.restrict V.ι)
    (restrictModuleSection V.ι ML
      (pullbackSection g M (isIso_pullbackUnitComparison g) σ)))
  have hgeom := fieldBaseChangeOpenPointCoordinateEvaluation_globalPullback
    base M U I (C.trivialization ij.1) xU hx σ a
  have hground := C.projectiveSectionSurfaceBasisCoordinateEvaluation_restrict
    base M ij r a k
  dsimp only at hgeom hground
  let qU := moduleRestrictTopLinearEquivOpenSectionsOver base M U
  let z := schemeModuleSectionsEquivTop (M.restrict U.ι)
    (restrictModuleSection U.ι M σ)
  have hcancel : qU.symm (qU z) = z := qU.symm_apply_apply z
  have hval := congrArg (fun w => fieldPointΓevaluation xU
    (moduleOpenTopLinearEquivOfFreeIsoOver (U.ι ≫ base) I
      (M.restrict U.ι)
      (localFreeIsoOfOver U I (C.trivialization ij.1) ≪≫
        (Scheme.Modules.overFunctorEquiv U).app M) w a)) hcancel
  exact hgeom.trans (hval.trans hground.symm)

/-- The linear coordinate evaluator on a pulled-back ground basis section
has the exact surface-chart value used by descent. -/
theorem SchemeModuleFiniteFreeAffineCover.fieldBaseChangeOpenPointCoordinateEvaluationLinearMap_basis_eq_surface
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    (r : Spec (.of L) ⟶
      (C.projectiveSectionOpenCover base M).X ij)
    (hx : (r ≫ C.projectiveSectionOpenCoverToSurfaceChart base M ij) ≫
      ((C.U ij.1).ι ≫ base) =
      Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (a : I)
    (k : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    let U := C.U ij.1
    let xU := r ≫ C.projectiveSectionOpenCoverToSurfaceChart base M ij
    let g := schemeFieldBaseChangeToOriginal (L := L) base
    let V := g ⁻¹ᵁ U
    let ML := (Scheme.Modules.pullback g).obj M
    let pL := schemeFieldBaseChangeToField (L := L) base
    letI : IsAffine (U : Scheme.{u}) := C.affine ij.1
    let qV := moduleRestrictTopLinearEquivOpenSectionsOver pL ML V
    let σ := schemeModuleGlobalSectionsOverEquivSections base M
      (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) k)
    let sV := qV (schemeModuleSectionsEquivTop (ML.restrict V.ι)
      (restrictModuleSection V.ι ML
        (pullbackSection g M (isIso_pullbackUnitComparison g) σ)))
    fieldBaseChangeOpenPointCoordinateEvaluationLinearMap base M U I
        (C.trivialization ij.1) xU hx a sV =
      C.projectiveSectionSurfaceBasisCoordinateEvaluation base M ij r a k := by
  dsimp only
  let U := C.U ij.1
  let xU := r ≫ C.projectiveSectionOpenCoverToSurfaceChart base M ij
  let g := schemeFieldBaseChangeToOriginal (L := L) base
  let V := g ⁻¹ᵁ U
  let ML := (Scheme.Modules.pullback g).obj M
  let pL := schemeFieldBaseChangeToField (L := L) base
  letI : IsAffine (U : Scheme.{u}) := C.affine ij.1
  let qV := moduleRestrictTopLinearEquivOpenSectionsOver pL ML V
  let σ := schemeModuleGlobalSectionsOverEquivSections base M
    (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) k)
  let sV := qV (schemeModuleSectionsEquivTop (ML.restrict V.ι)
    (restrictModuleSection V.ι ML
      (pullbackSection g M (isIso_pullbackUnitComparison g) σ)))
  rw [fieldBaseChangeOpenPointCoordinateEvaluationLinearMap_apply]
  have hpoint := C.fieldBaseChangeOpenPointCoordinateEvaluation_basis_eq_surface
    base M ij r hx a k
  dsimp only at hpoint
  exact hpoint

/-- The actual global-section coordinate functional takes the prescribed
surface-chart value on each pulled-back ground basis section. -/
theorem SchemeModuleFiniteFreeAffineCover.fieldBaseChangeGlobalPointCoordinateEvaluationLinearMap_basis_eq_surface
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    (r : Spec (.of L) ⟶
      (C.projectiveSectionOpenCover base M).X ij)
    (hx : (r ≫ C.projectiveSectionOpenCoverToSurfaceChart base M ij) ≫
      ((C.U ij.1).ι ≫ base) =
      Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (a : I)
    (k : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    let U := C.U ij.1
    let xU := r ≫ C.projectiveSectionOpenCoverToSurfaceChart base M ij
    let g := schemeFieldBaseChangeToOriginal (L := L) base
    let ML := (Scheme.Modules.pullback g).obj M
    let pL := schemeFieldBaseChangeToField (L := L) base
    letI : IsAffine (U : Scheme.{u}) := C.affine ij.1
    let σ := schemeModuleGlobalSectionsOverEquivSections base M
      (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) k)
    let σL := pullbackSection g M (isIso_pullbackUnitComparison g) σ
    fieldBaseChangeGlobalPointCoordinateEvaluationLinearMap base M U I
        (C.trivialization ij.1) xU hx a
        ((schemeModuleGlobalSectionsOverEquivSections pL ML).symm σL) =
      C.projectiveSectionSurfaceBasisCoordinateEvaluation base M ij r a k := by
  dsimp only
  let U := C.U ij.1
  let xU := r ≫ C.projectiveSectionOpenCoverToSurfaceChart base M ij
  let g := schemeFieldBaseChangeToOriginal (L := L) base
  let V := g ⁻¹ᵁ U
  let ML := (Scheme.Modules.pullback g).obj M
  let pL := schemeFieldBaseChangeToField (L := L) base
  letI : IsAffine (U : Scheme.{u}) := C.affine ij.1
  let σ := schemeModuleGlobalSectionsOverEquivSections base M
    (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) k)
  let σL := pullbackSection g M (isIso_pullbackUnitComparison g) σ
  rw [fieldBaseChangeGlobalPointCoordinateEvaluationLinearMap_apply]
  exact C.fieldBaseChangeOpenPointCoordinateEvaluationLinearMap_basis_eq_surface
    base M ij r hx a k


end

end PfaffianDescent
