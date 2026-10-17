import PfaffianDescent.VoisinFieldBaseChangePointEvaluation
import PfaffianDescent.VoisinFieldBaseChangeGlobalComparison

/-!
# Field-point evaluation of canonical pulled-back open sections

The affine-open coordinate formula is expressed here for the intrinsic
pullback of an open module section.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory BundleSectionZeroLocus
open scoped TensorProduct

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false in
/-- At the canonical lifted field point, coordinates of the intrinsic
pullback of an open module section evaluate as the original coordinates. -/
theorem fieldPointΓevaluation_schemeFieldBaseChangeOpenPullbackSection_coord_canonical
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (M : X.Modules) (U : X.Opens) [IsAffine (U : Scheme.{u})]
    (I : Type u) [Fintype I] [DecidableEq I]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (xU : Spec (.of L) ⟶ (U : Scheme.{u}))
    (hxU : xU ≫ (U.ι ≫ base) =
      Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (s : SchemeModuleOpenSectionsOver base M U) (i : I) :
    let g := schemeFieldBaseChangeToOriginal (L := L) base
    let V := g ⁻¹ᵁ U
    let ML := (Scheme.Modules.pullback g).obj M
    let pU := U.ι ≫ base
    let pV := V.ι ≫ schemeFieldBaseChangeToField (L := L) base
    let eU := localFreeIsoOfOver U I t ≪≫
      (Scheme.Modules.overFunctorEquiv U).app M
    let eV := schemeFieldBaseChangeOpenRestrictedFreeIso base M U I t
    let qU := moduleRestrictTopLinearEquivOpenSectionsOver base M U
    let qV := moduleRestrictTopLinearEquivOpenSectionsOver
      (schemeFieldBaseChangeToField (L := L) base) ML V
    fieldPointΓevaluation
        (schemeFieldBaseChangeOpenPoint base U xU hxU)
        (moduleOpenTopLinearEquivOfFreeIsoOver pV I (ML.restrict V.ι) eV
          (qV.symm (schemeFieldBaseChangeOpenPullbackSection
            (L := L) base M U s)) i) =
      fieldPointΓevaluation xU
        (moduleOpenTopLinearEquivOfFreeIsoOver pU I (M.restrict U.ι) eU
          (qU.symm s) i) := by
  dsimp only
  have h := fieldPointΓevaluation_schemeFieldBaseChangeOpenFreeModuleSections_tmul_coord_canonical
    base M U I t xU hxU 1 s i
  dsimp only at h
  let g := schemeFieldBaseChangeToOriginal (L := L) base
  let V := g ⁻¹ᵁ U
  let ML := (Scheme.Modules.pullback g).obj M
  let pV := V.ι ≫ schemeFieldBaseChangeToField (L := L) base
  let eV := schemeFieldBaseChangeOpenRestrictedFreeIso (L := L) base M U I t
  let qV := moduleRestrictTopLinearEquivOpenSectionsOver
    (schemeFieldBaseChangeToField (L := L) base) ML V
  let xV := schemeFieldBaseChangeOpenPoint (L := L) base U xU hxU
  have hsec : schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv
      base M U I t ((1 : L) ⊗ₜ[K] s) =
      schemeFieldBaseChangeOpenPullbackSection (L := L) base M U s := by
    simpa only [one_smul] using
      schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv_tmul_eq_smul_pullback
        base M U I t (1 : L) s
  simpa only [hsec, one_mul] using h




/-- Coordinate evaluation on the inverse-image affine open at the
canonical lift of a field-valued point. Keeping this evaluator named makes
section-transport equalities small enough to elaborate at default limits. -/
noncomputable def fieldBaseChangeOpenPointCoordinateEvaluation
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (M : X.Modules) (U : X.Opens) [IsAffine (U : Scheme.{u})]
    (I : Type u) [Fintype I] [DecidableEq I]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (xU : Spec (.of L) ⟶ (U : Scheme.{u}))
    (hxU : xU ≫ (U.ι ≫ base) =
      Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (i : I) :
    let g := schemeFieldBaseChangeToOriginal (L := L) base
    let V := g ⁻¹ᵁ U
    let ML := (Scheme.Modules.pullback g).obj M
    SchemeModuleOpenSectionsOver
      (schemeFieldBaseChangeToField (L := L) base) ML V → L := by
  let g := schemeFieldBaseChangeToOriginal (L := L) base
  let V := g ⁻¹ᵁ U
  let ML := (Scheme.Modules.pullback g).obj M
  let pL := schemeFieldBaseChangeToField (L := L) base
  let pV := V.ι ≫ pL
  let eV := schemeFieldBaseChangeOpenRestrictedFreeIso (L := L) base M U I t
  let qV := moduleRestrictTopLinearEquivOpenSectionsOver pL ML V
  let xV := schemeFieldBaseChangeOpenPoint (L := L) base U xU hxU
  exact fun z => fieldPointΓevaluation xV
    (moduleOpenTopLinearEquivOfFreeIsoOver pV I (ML.restrict V.ι) eV
      (qV.symm z) i)

theorem fieldBaseChangeOpenPointCoordinateEvaluation_pullback
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (M : X.Modules) (U : X.Opens) [IsAffine (U : Scheme.{u})]
    (I : Type u) [Fintype I] [DecidableEq I]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (xU : Spec (.of L) ⟶ (U : Scheme.{u}))
    (hxU : xU ≫ (U.ι ≫ base) =
      Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (s : SchemeModuleOpenSectionsOver base M U) (i : I) :
    fieldBaseChangeOpenPointCoordinateEvaluation base M U I t xU hxU i
      (schemeFieldBaseChangeOpenPullbackSection (L := L) base M U s) =
      fieldPointΓevaluation xU
        (moduleOpenTopLinearEquivOfFreeIsoOver (U.ι ≫ base) I
          (M.restrict U.ι)
          (localFreeIsoOfOver U I t ≪≫
            (Scheme.Modules.overFunctorEquiv U).app M)
          ((moduleRestrictTopLinearEquivOpenSectionsOver base M U).symm s) i) := by
  exact fieldPointΓevaluation_schemeFieldBaseChangeOpenPullbackSection_coord_canonical
    base M U I t xU hxU s i

/-- The named coordinate evaluator gives the same value on a
restricted global pullback as on the original section at the projected
field point. -/
theorem fieldBaseChangeOpenPointCoordinateEvaluation_globalPullback
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (M : X.Modules) (U : X.Opens) [IsAffine (U : Scheme.{u})]
    (I : Type u) [Fintype I] [DecidableEq I]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (xU : Spec (.of L) ⟶ (U : Scheme.{u}))
    (hxU : xU ≫ (U.ι ≫ base) =
      Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (σ : M.sections) (i : I) :
    let g := schemeFieldBaseChangeToOriginal (L := L) base
    let V := g ⁻¹ᵁ U
    let ML := (Scheme.Modules.pullback g).obj M
    let pL := schemeFieldBaseChangeToField (L := L) base
    let qU := moduleRestrictTopLinearEquivOpenSectionsOver base M U
    let qV := moduleRestrictTopLinearEquivOpenSectionsOver pL ML V
    let sU := qU (schemeModuleSectionsEquivTop (M.restrict U.ι)
      (restrictModuleSection U.ι M σ))
    let sV := qV (schemeModuleSectionsEquivTop (ML.restrict V.ι)
      (restrictModuleSection V.ι ML
        (pullbackSection g M (isIso_pullbackUnitComparison g) σ)))
    fieldBaseChangeOpenPointCoordinateEvaluation base M U I t xU hxU i sV =
      fieldPointΓevaluation xU
        (moduleOpenTopLinearEquivOfFreeIsoOver (U.ι ≫ base) I
          (M.restrict U.ι)
          (localFreeIsoOfOver U I t ≪≫
            (Scheme.Modules.overFunctorEquiv U).app M)
          (qU.symm sU) i) := by
  dsimp only
  let g := schemeFieldBaseChangeToOriginal (L := L) base
  let V := g ⁻¹ᵁ U
  let ML := (Scheme.Modules.pullback g).obj M
  let pL := schemeFieldBaseChangeToField (L := L) base
  let qU := moduleRestrictTopLinearEquivOpenSectionsOver base M U
  let qV := moduleRestrictTopLinearEquivOpenSectionsOver pL ML V
  let sU := qU (schemeModuleSectionsEquivTop (M.restrict U.ι)
    (restrictModuleSection U.ι M σ))
  let sV := qV (schemeModuleSectionsEquivTop (ML.restrict V.ι)
    (restrictModuleSection V.ι ML
      (pullbackSection g M (isIso_pullbackUnitComparison g) σ)))
  have hsec : schemeFieldBaseChangeOpenPullbackSection
      (L := L) base M U sU = sV :=
    schemeFieldBaseChangeOpenPullback_of_restricted_global
      (L := L) base M U σ
  calc
    fieldBaseChangeOpenPointCoordinateEvaluation base M U I t xU hxU i sV =
        fieldBaseChangeOpenPointCoordinateEvaluation base M U I t xU hxU i
          (schemeFieldBaseChangeOpenPullbackSection (L := L) base M U sU) :=
            congrArg
              (fieldBaseChangeOpenPointCoordinateEvaluation
                base M U I t xU hxU i) hsec.symm
    _ = _ := fieldBaseChangeOpenPointCoordinateEvaluation_pullback
      base M U I t xU hxU sU i

end

end PfaffianDescent
