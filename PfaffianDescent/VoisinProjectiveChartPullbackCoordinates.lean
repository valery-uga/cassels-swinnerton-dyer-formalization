import PfaffianDescent.VoisinFixedLinearSystemUniversalFamily
import PfaffianDescent.VoisinFieldBaseChangeOpenCanonicalPullback

/-!
# Coordinates on a surface--parameter product chart

The projective-section chart frame is the pullback of the frame on its
underlying affine surface open, followed by canonical module isomorphisms.
This file identifies its coordinates with pullbacks of the surface-open
coordinates.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory BundleSectionZeroLocus

universe u

noncomputable section

/-- The coordinate of a locally pulled-back section on a projective-section
product chart is the pullback of its coordinate on the underlying surface
open. -/
theorem SchemeModuleFiniteFreeAffineCover.projectiveSectionLocalFreeIso_coordinate_pullback
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    (sU : ((Scheme.Modules.overEquiv (C.U ij.1)).functor.obj
      (M.over (C.U ij.1))).sections) (i : I) :
    let p := C.projectiveSectionOpenCoverToSurfaceChart base M ij
    let eU := localFreeIsoOfOver (C.U ij.1) I (C.trivialization ij.1)
    let A := (Scheme.Modules.pullback p).mapIso
        ((Scheme.Modules.overFunctorEquiv (C.U ij.1)).app M ≪≫
          (Scheme.Modules.restrictFunctorIsoPullback (C.U ij.1).ι).app M) ≪≫
      (Scheme.Modules.pullbackComp p (C.U ij.1).ι).app M
    let sP := pullbackSection p
      ((Scheme.Modules.overEquiv (C.U ij.1)).functor.obj (M.over (C.U ij.1)))
      (isIso_pullbackUnitComparison p) sU
    moduleOpenTopLinearEquivOfFreeIso I
        (C.projectiveSectionLocalModule base M ij)
        (C.projectiveSectionLocalFreeIso base M ij)
        (schemeModuleSectionsEquivTop _
          (SheafOfModules.sectionsMap A.hom sP)) i =
      p.appTop.hom
        (moduleOpenTopLinearEquivOfFreeIso I
          ((Scheme.Modules.overEquiv (C.U ij.1)).functor.obj
            (M.over (C.U ij.1))) eU
          (schemeModuleSectionsEquivTop _ sU) i) := by
  dsimp only
  let p := C.projectiveSectionOpenCoverToSurfaceChart base M ij
  let eU := localFreeIsoOfOver (C.U ij.1) I (C.trivialization ij.1)
  let A := (Scheme.Modules.pullback p).mapIso
      ((Scheme.Modules.overFunctorEquiv (C.U ij.1)).app M ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback (C.U ij.1).ι).app M) ≪≫
    (Scheme.Modules.pullbackComp p (C.U ij.1).ι).app M
  let sP := pullbackSection p
    ((Scheme.Modules.overEquiv (C.U ij.1)).functor.obj (M.over (C.U ij.1)))
    (isIso_pullbackUnitComparison p) sU
  change moduleOpenTopLinearEquivOfFreeIso I
      (C.projectiveSectionLocalModule base M ij)
      (pullbackFreeIso p I eU ≪≫ A)
      (schemeModuleSectionsEquivTop _ (SheafOfModules.sectionsMap A.hom sP)) i = _
  have hpost := module_coordinate_postcompose I (pullbackFreeIso p I eU) A
    (schemeModuleSectionsEquivTop _ sP) i
  have hs : schemeModuleSectionsEquivTop _
      (SheafOfModules.sectionsMap A.hom sP) =
      (A.hom.val.app (Opposite.op ⊤)).hom
        (schemeModuleSectionsEquivTop _ sP) := rfl
  rw [hs]
  change moduleOpenTopLinearEquivOfFreeIso I
      ((Scheme.Modules.pullback (p ≫ (C.U ij.1).ι)).obj M)
      (pullbackFreeIso p I eU ≪≫ A)
      ((A.hom.val.app (Opposite.op ⊤)).hom
        (schemeModuleSectionsEquivTop _ sP)) i = _
  have hgen := moduleOpenTopLinearEquivOfPullbackFreeIso_general p I
    ((Scheme.Modules.overEquiv (C.U ij.1)).functor.obj
      (M.over (C.U ij.1))) eU
      (schemeModuleSectionsEquivTop _ sU) i
  have hgen' : moduleOpenTopLinearEquivOfFreeIso I
      ((Scheme.Modules.pullback p).obj
        ((Scheme.Modules.overEquiv (C.U ij.1)).functor.obj
          (M.over (C.U ij.1))))
      (pullbackFreeIso p I eU)
      (schemeModuleSectionsEquivTop _ sP) i =
      p.appTop.hom
        (moduleOpenTopLinearEquivOfFreeIso I
          ((Scheme.Modules.overEquiv (C.U ij.1)).functor.obj
            (M.over (C.U ij.1))) eU
          (schemeModuleSectionsEquivTop _ sU) i) := by
    simpa only [Equiv.symm_apply_apply] using hgen
  exact hpost.trans hgen'

/-- A global section restricted to the chosen surface open, transported
through the chart's module presentation, and then pulled to the product
chart is the direct pullback of that global section from the surface. -/
theorem SchemeModuleFiniteFreeAffineCover.projectiveSectionLocalSection_globalPullback
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    (s : M.sections) :
    let p := C.projectiveSectionOpenCoverToSurfaceChart base M ij
    let q := (C.U ij.1).ι
    let B := (Scheme.Modules.overFunctorEquiv (C.U ij.1)).app M ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback q).app M
    let A := (Scheme.Modules.pullback p).mapIso B ≪≫
      (Scheme.Modules.pullbackComp p q).app M
    let sU := SheafOfModules.sectionsMap B.inv
      (pullbackSection q M (isIso_pullbackUnitComparison q) s)
    let sP := pullbackSection p
      ((Scheme.Modules.overEquiv (C.U ij.1)).functor.obj (M.over (C.U ij.1)))
      (isIso_pullbackUnitComparison p) sU
    SheafOfModules.sectionsMap A.hom sP =
      pullbackSection (p ≫ q) M
        (isIso_pullbackUnitComparison (p ≫ q)) s := by
  dsimp only
  let p := C.projectiveSectionOpenCoverToSurfaceChart base M ij
  let q := (C.U ij.1).ι
  let B := (Scheme.Modules.overFunctorEquiv (C.U ij.1)).app M ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback q).app M
  let A := (Scheme.Modules.pullback p).mapIso B ≪≫
    (Scheme.Modules.pullbackComp p q).app M
  let sU := SheafOfModules.sectionsMap B.inv
    (pullbackSection q M (isIso_pullbackUnitComparison q) s)
  let sP := pullbackSection p
    ((Scheme.Modules.overEquiv (C.U ij.1)).functor.obj (M.over (C.U ij.1)))
    (isIso_pullbackUnitComparison p) sU
  have hB : SheafOfModules.sectionsMap B.hom sU =
      pullbackSection q M (isIso_pullbackUnitComparison q) s := by
    change SheafOfModules.sectionsMap B.hom
      (SheafOfModules.sectionsMap B.inv
        (pullbackSection q M (isIso_pullbackUnitComparison q) s)) = _
    calc
      _ = SheafOfModules.sectionsMap (B.inv ≫ B.hom)
            (pullbackSection q M (isIso_pullbackUnitComparison q) s) :=
          (SheafOfModules.sectionsMap_comp B.inv B.hom _).symm
      _ = SheafOfModules.sectionsMap (𝟙 _)
            (pullbackSection q M (isIso_pullbackUnitComparison q) s) :=
          congrArg (fun z => SheafOfModules.sectionsMap z
            (pullbackSection q M (isIso_pullbackUnitComparison q) s)) B.inv_hom_id
      _ = _ := SheafOfModules.sectionsMap_id _
  have hcomp : SheafOfModules.sectionsMap
      ((Scheme.Modules.pullbackComp p q).app M).hom
      (pullbackSection p ((Scheme.Modules.pullback q).obj M)
        (isIso_pullbackUnitComparison p)
        (pullbackSection q M (isIso_pullbackUnitComparison q) s)) =
      pullbackSection (p ≫ q) M
        (isIso_pullbackUnitComparison (p ≫ q)) s := by
    let D := (Scheme.Modules.pullbackComp p q).app M
    have hraw := pullbackSection_comp p q M
      (isIso_pullbackUnitComparison p)
      (isIso_pullbackUnitComparison q)
      (isIso_pullbackUnitComparison (p ≫ q)) s
    calc
      _ = SheafOfModules.sectionsMap D.hom
            (SheafOfModules.sectionsMap D.inv
              (pullbackSection (p ≫ q) M
                (isIso_pullbackUnitComparison (p ≫ q)) s)) :=
          congrArg (SheafOfModules.sectionsMap D.hom) hraw.symm
      _ = SheafOfModules.sectionsMap (D.inv ≫ D.hom)
            (pullbackSection (p ≫ q) M
              (isIso_pullbackUnitComparison (p ≫ q)) s) :=
          (SheafOfModules.sectionsMap_comp D.inv D.hom _).symm
      _ = SheafOfModules.sectionsMap (𝟙 _)
            (pullbackSection (p ≫ q) M
              (isIso_pullbackUnitComparison (p ≫ q)) s) :=
          congrArg (fun z => SheafOfModules.sectionsMap z
            (pullbackSection (p ≫ q) M
              (isIso_pullbackUnitComparison (p ≫ q)) s)) D.inv_hom_id
      _ = _ := SheafOfModules.sectionsMap_id _
  calc
    SheafOfModules.sectionsMap A.hom sP =
        SheafOfModules.sectionsMap
          ((Scheme.Modules.pullbackComp p q).app M).hom
          (SheafOfModules.sectionsMap
            ((Scheme.Modules.pullback p).map B.hom) sP) := by
              exact SheafOfModules.sectionsMap_comp _ _ sP
    _ = SheafOfModules.sectionsMap
          ((Scheme.Modules.pullbackComp p q).app M).hom
          (pullbackSection p ((Scheme.Modules.pullback q).obj M)
            (isIso_pullbackUnitComparison p)
            (pullbackSection q M (isIso_pullbackUnitComparison q) s)) := by
              change SheafOfModules.sectionsMap _
                (SheafOfModules.sectionsMap _
                  (pullbackSection p _ (isIso_pullbackUnitComparison p) sU)) = _
              rw [sectionsMap_pullbackSection, hB]
    _ = pullbackSection (p ≫ q) M
          (isIso_pullbackUnitComparison (p ≫ q)) s := by
            exact hcomp

/-- At a field-valued point of the surface--parameter product chart, the
coordinate of a pulled-back section evaluates to the coordinate evaluated
at the projected point of the underlying surface chart. -/
theorem SchemeModuleFiniteFreeAffineCover.projectiveSectionLocalFreeIso_coordinate_fieldPoint
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    (sU : ((Scheme.Modules.overEquiv (C.U ij.1)).functor.obj
      (M.over (C.U ij.1))).sections) (i : I)
    {L : Type u} [Field L]
    (r : Spec (.of L) ⟶
      (C.projectiveSectionOpenCover base M).X ij) :
    let p := C.projectiveSectionOpenCoverToSurfaceChart base M ij
    let eU := localFreeIsoOfOver (C.U ij.1) I (C.trivialization ij.1)
    let A := (Scheme.Modules.pullback p).mapIso
        ((Scheme.Modules.overFunctorEquiv (C.U ij.1)).app M ≪≫
          (Scheme.Modules.restrictFunctorIsoPullback (C.U ij.1).ι).app M) ≪≫
      (Scheme.Modules.pullbackComp p (C.U ij.1).ι).app M
    let sP := pullbackSection p
      ((Scheme.Modules.overEquiv (C.U ij.1)).functor.obj (M.over (C.U ij.1)))
      (isIso_pullbackUnitComparison p) sU
    fieldPointΓevaluation r
      (moduleOpenTopLinearEquivOfFreeIso I
        (C.projectiveSectionLocalModule base M ij)
        (C.projectiveSectionLocalFreeIso base M ij)
        (schemeModuleSectionsEquivTop _
          (SheafOfModules.sectionsMap A.hom sP)) i) =
    fieldPointΓevaluation (r ≫ p)
      (moduleOpenTopLinearEquivOfFreeIso I
        ((Scheme.Modules.overEquiv (C.U ij.1)).functor.obj
          (M.over (C.U ij.1))) eU
        (schemeModuleSectionsEquivTop _ sU) i) := by
  dsimp only
  rw [C.projectiveSectionLocalFreeIso_coordinate_pullback base M ij sU i]
  exact (fieldPointΓevaluation_comp r
    (C.projectiveSectionOpenCoverToSurfaceChart base M ij) _).symm

/-- The chart coordinate of the direct pullback of a global section is
evaluated on the surface chart after restricting that global section. -/
theorem SchemeModuleFiniteFreeAffineCover.projectiveSectionGlobalPullback_coordinate_fieldPoint
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    (s : M.sections) (i : I)
    {L : Type u} [Field L]
    (r : Spec (.of L) ⟶
      (C.projectiveSectionOpenCover base M).X ij) :
    let p := C.projectiveSectionOpenCoverToSurfaceChart base M ij
    let q := (C.U ij.1).ι
    let B := (Scheme.Modules.overFunctorEquiv (C.U ij.1)).app M ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback q).app M
    let sU := SheafOfModules.sectionsMap B.inv
      (pullbackSection q M (isIso_pullbackUnitComparison q) s)
    let eU := localFreeIsoOfOver (C.U ij.1) I (C.trivialization ij.1)
    fieldPointΓevaluation r
      (sectionCoordinateOfFreeIso I
        (C.projectiveSectionLocalFreeIso base M ij)
        (pullbackSection (p ≫ q) M
          (isIso_pullbackUnitComparison (p ≫ q)) s) i) =
      fieldPointΓevaluation (r ≫ p)
        (sectionCoordinateOfFreeIso I eU sU i) := by
  dsimp only
  let p := C.projectiveSectionOpenCoverToSurfaceChart base M ij
  let q := (C.U ij.1).ι
  let B := (Scheme.Modules.overFunctorEquiv (C.U ij.1)).app M ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback q).app M
  let sU := SheafOfModules.sectionsMap B.inv
    (pullbackSection q M (isIso_pullbackUnitComparison q) s)
  have hpoint := C.projectiveSectionLocalFreeIso_coordinate_fieldPoint
    base M ij sU i r
  have hsection := C.projectiveSectionLocalSection_globalPullback
    base M ij s
  dsimp only at hpoint hsection
  rw [moduleOpenTopLinearEquivOfFreeIso_eq_freeSectionCoordinate,
    moduleOpenTopLinearEquivOfFreeIso_eq_freeSectionCoordinate] at hpoint
  simp only [Equiv.symm_apply_apply] at hpoint
  rw [hsection] at hpoint
  exact hpoint

/-- The ground evaluation functional used by the descent endpoint has
the surface-open coordinate interpretation on each member of its chosen
finite basis. -/
theorem SchemeModuleFiniteFreeAffineCover.projectiveSectionLocalBasisCoordinateEvaluationLinearMap_finBasis_surface
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    (r : Spec (.of L) ⟶
      (C.projectiveSectionOpenCover base M).X ij)
    (a : I)
    (k : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    let p := C.projectiveSectionOpenCoverToSurfaceChart base M ij
    let q := (C.U ij.1).ι
    let B := (Scheme.Modules.overFunctorEquiv (C.U ij.1)).app M ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback q).app M
    let s := schemeModuleGlobalSectionsOverEquivSections base M
      (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) k)
    let sU := SheafOfModules.sectionsMap B.inv
      (pullbackSection q M (isIso_pullbackUnitComparison q) s)
    let eU := localFreeIsoOfOver (C.U ij.1) I (C.trivialization ij.1)
    C.projectiveSectionLocalBasisCoordinateEvaluationLinearMap
        base M ij r a
        (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) k) =
      fieldPointΓevaluation (r ≫ p)
        (sectionCoordinateOfFreeIso I eU sU a) := by
  dsimp only
  rw [C.projectiveSectionLocalBasisCoordinateEvaluationLinearMap_finBasis
    base M ij r a k]
  exact C.projectiveSectionGlobalPullback_coordinate_fieldPoint
    base M ij
    (schemeModuleGlobalSectionsOverEquivSections base M
      (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) k))
    a r

/-- Surface-open form of one finite-basis coordinate value. This is the
form directly compared with geometric evaluation after field base change. -/
noncomputable def SchemeModuleFiniteFreeAffineCover.projectiveSectionSurfaceBasisCoordinateEvaluation
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    (r : Spec (.of L) ⟶
      (C.projectiveSectionOpenCover base M).X ij)
    (a : I)
    (k : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) : L :=
  let p := C.projectiveSectionOpenCoverToSurfaceChart base M ij
  let q := (C.U ij.1).ι
  let B := (Scheme.Modules.overFunctorEquiv (C.U ij.1)).app M ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback q).app M
  let s := schemeModuleGlobalSectionsOverEquivSections base M
    (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) k)
  let sU := SheafOfModules.sectionsMap B.inv
    (pullbackSection q M (isIso_pullbackUnitComparison q) s)
  let eU := localFreeIsoOfOver (C.U ij.1) I (C.trivialization ij.1)
  fieldPointΓevaluation (r ≫ p)
    (sectionCoordinateOfFreeIso I eU sU a)

theorem SchemeModuleFiniteFreeAffineCover.projectiveSectionLocalBasisCoordinateEvaluationLinearMap_finBasis_eq_surface
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    (r : Spec (.of L) ⟶
      (C.projectiveSectionOpenCover base M).X ij)
    (a : I)
    (k : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    C.projectiveSectionLocalBasisCoordinateEvaluationLinearMap base M ij r a
      (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) k) =
    C.projectiveSectionSurfaceBasisCoordinateEvaluation base M ij r a k :=
  C.projectiveSectionLocalBasisCoordinateEvaluationLinearMap_finBasis_surface
    base M ij r a k


/-- The surface-open section presentation used for the projective
chart becomes the ordinary restricted global section after transport
through the canonical over-functor equivalence. -/
theorem SchemeModuleFiniteFreeAffineCover.projectiveSectionSurfaceOpenSection_transport
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    (s : M.sections) :
    let q := (C.U ij.1).ι
    let T := (Scheme.Modules.overFunctorEquiv (C.U ij.1)).app M
    let B := T ≪≫ (Scheme.Modules.restrictFunctorIsoPullback q).app M
    let sU := SheafOfModules.sectionsMap B.inv
      (pullbackSection q M (isIso_pullbackUnitComparison q) s)
    SheafOfModules.sectionsMap T.hom sU =
      restrictModuleSection q M s := by
  dsimp only
  let q := (C.U ij.1).ι
  let T := (Scheme.Modules.overFunctorEquiv (C.U ij.1)).app M
  let R := (Scheme.Modules.restrictFunctorIsoPullback q).app M
  let B := T ≪≫ R
  let sU := SheafOfModules.sectionsMap B.inv
    (pullbackSection q M (isIso_pullbackUnitComparison q) s)
  have h :=
    sectionsMap_restrictModuleSection_eq_pullbackSection q
      (isIso_pullbackUnitComparison q) T.symm s
  have h' : SheafOfModules.sectionsMap T.inv
      (restrictModuleSection q M s) = sU := by
    change SheafOfModules.sectionsMap T.inv
      (restrictModuleSection q M s) =
      SheafOfModules.sectionsMap (R.inv ≫ T.inv)
        (pullbackSection q M (isIso_pullbackUnitComparison q) s) at h
    exact h
  calc
    SheafOfModules.sectionsMap T.hom sU =
        SheafOfModules.sectionsMap T.hom
          (SheafOfModules.sectionsMap T.inv
            (restrictModuleSection q M s)) :=
      congrArg (SheafOfModules.sectionsMap T.hom) h'.symm
    _ = SheafOfModules.sectionsMap (T.inv ≫ T.hom)
          (restrictModuleSection q M s) :=
      (SheafOfModules.sectionsMap_comp T.inv T.hom _).symm
    _ = SheafOfModules.sectionsMap (𝟙 _) (restrictModuleSection q M s) :=
      congrArg (fun z => SheafOfModules.sectionsMap z
        (restrictModuleSection q M s)) T.inv_hom_id
    _ = restrictModuleSection q M s := SheafOfModules.sectionsMap_id _

/-- The surface-open free coordinate used by the projective-chart
basis formula agrees with the coordinate of the ordinary restricted
global section in the canonical restricted-module frame. -/
theorem SchemeModuleFiniteFreeAffineCover.projectiveSectionSurfaceCoordinate_restrict
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    (s : M.sections) (i : I) :
    let U := C.U ij.1
    let q := U.ι
    let T := (Scheme.Modules.overFunctorEquiv U).app M
    let B := T ≪≫ (Scheme.Modules.restrictFunctorIsoPullback q).app M
    let sU := SheafOfModules.sectionsMap B.inv
      (pullbackSection q M (isIso_pullbackUnitComparison q) s)
    let eU := localFreeIsoOfOver U I (C.trivialization ij.1)
    sectionCoordinateOfFreeIso I eU sU i =
      moduleOpenTopLinearEquivOfFreeIso I (M.restrict q) (eU ≪≫ T)
        (schemeModuleSectionsEquivTop (M.restrict q)
          (restrictModuleSection q M s)) i := by
  dsimp only
  let U := C.U ij.1
  let q := U.ι
  let T := (Scheme.Modules.overFunctorEquiv U).app M
  let B := T ≪≫ (Scheme.Modules.restrictFunctorIsoPullback q).app M
  let sU := SheafOfModules.sectionsMap B.inv
    (pullbackSection q M (isIso_pullbackUnitComparison q) s)
  let eU := localFreeIsoOfOver U I (C.trivialization ij.1)
  have hsec := C.projectiveSectionSurfaceOpenSection_transport base M ij s
  dsimp only at hsec
  have htop : (T.hom.val.app (Opposite.op ⊤)).hom
      (schemeModuleSectionsEquivTop _ sU) =
      schemeModuleSectionsEquivTop (M.restrict q)
        (restrictModuleSection q M s) := by
    exact congrArg (schemeModuleSectionsEquivTop (M.restrict q)) hsec
  have hpost := module_coordinate_postcompose I eU T
    (schemeModuleSectionsEquivTop _ sU) i
  have htop' : (T.hom.val.app (Opposite.op ⊤)).hom
      (schemeModuleSectionsEquivTop
        ((Scheme.Modules.overEquiv U).functor.obj (M.over U)) sU) =
      schemeModuleSectionsEquivTop (M.restrict q)
        (restrictModuleSection q M s) := htop
  rw [htop'] at hpost
  rw [moduleOpenTopLinearEquivOfFreeIso_eq_freeSectionCoordinate I
    ((Scheme.Modules.overEquiv U).functor.obj (M.over U)) eU
    (schemeModuleSectionsEquivTop _ sU) i] at hpost
  rw [(schemeModuleSectionsEquivTop
    ((Scheme.Modules.overEquiv U).functor.obj (M.over U))).symm_apply_apply] at hpost
  exact hpost.symm

/-- The endpoint's surface basis value is the ordinary restricted
global-section coordinate at the projected surface point. -/
theorem SchemeModuleFiniteFreeAffineCover.projectiveSectionSurfaceBasisCoordinateEvaluation_restrict
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    (r : Spec (.of L) ⟶
      (C.projectiveSectionOpenCover base M).X ij)
    (a : I)
    (k : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    let U := C.U ij.1
    let q := U.ι
    let p := C.projectiveSectionOpenCoverToSurfaceChart base M ij
    let σ := schemeModuleGlobalSectionsOverEquivSections base M
      (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) k)
    let e := localFreeIsoOfOver U I (C.trivialization ij.1) ≪≫
      (Scheme.Modules.overFunctorEquiv U).app M
    C.projectiveSectionSurfaceBasisCoordinateEvaluation base M ij r a k =
      fieldPointΓevaluation (r ≫ p)
        (moduleOpenTopLinearEquivOfFreeIsoOver (q ≫ base) I
          (M.restrict q) e
          (schemeModuleSectionsEquivTop (M.restrict q)
            (restrictModuleSection q M σ)) a) := by
  dsimp only
  have h := C.projectiveSectionSurfaceCoordinate_restrict base M ij
    (schemeModuleGlobalSectionsOverEquivSections base M
      (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) k)) a
  dsimp only at h
  exact congrArg (fieldPointΓevaluation
    (r ≫ C.projectiveSectionOpenCoverToSurfaceChart base M ij)) h

end

end PfaffianDescent
