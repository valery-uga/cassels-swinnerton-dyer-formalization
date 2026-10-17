import PfaffianDescent.VoisinFieldBaseChangeOpenPullbackPointEvaluation
import PfaffianDescent.VoisinGlobalOpenSectionRestriction

/-!
# Linear coordinate evaluation after field base change

A field-valued point on an inverse-image affine open evaluates each free
coordinate of a module section linearly over the extension field.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory BundleSectionZeroLocus

universe u

noncomputable section

/-- The canonical field-point coordinate evaluator as an extension-field
linear map on open module sections. -/
noncomputable def fieldBaseChangeOpenPointCoordinateEvaluationLinearMap
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
      (schemeFieldBaseChangeToField (L := L) base) ML V →ₗ[L] L := by
  let g := schemeFieldBaseChangeToOriginal (L := L) base
  let V := g ⁻¹ᵁ U
  let ML := (Scheme.Modules.pullback g).obj M
  let pL := schemeFieldBaseChangeToField (L := L) base
  let pV := V.ι ≫ pL
  let eV := schemeFieldBaseChangeOpenRestrictedFreeIso (L := L) base M U I t
  let qV := moduleRestrictTopLinearEquivOpenSectionsOver pL ML V
  let xV := schemeFieldBaseChangeOpenPoint (L := L) base U xU hxU
  have hxV : xV ≫ pV =
      Spec.map (CommRingCat.ofHom (algebraMap L L)) := by
    rw [schemeFieldBaseChangeOpenPoint_toField]
    simp
  let ev := fieldPointΓevaluationLinearMap pV xV hxV
  letI := Module.compHom Γ((V : Scheme.{u}), ⊤)
    (schemeOpenBaseRingHom pV ⊤)
  let coord := moduleOpenTopLinearEquivOfFreeIsoOver pV I
    (ML.restrict V.ι) eV
  exact ev.comp ((LinearMap.proj i).comp
    (coord.toLinearMap.comp qV.symm.toLinearMap))


/-- Coordinate evaluation after restricting a global section to the
inverse-image affine open, as an extension-field linear functional on the
global sections of the pulled-back module. -/
noncomputable def fieldBaseChangeGlobalPointCoordinateEvaluationLinearMap
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
    let ML := (Scheme.Modules.pullback g).obj M
    let pL := schemeFieldBaseChangeToField (L := L) base
    SchemeModuleGlobalSectionsOver pL ML →ₗ[L] L := by
  let g := schemeFieldBaseChangeToOriginal (L := L) base
  let V := g ⁻¹ᵁ U
  let ML := (Scheme.Modules.pullback g).obj M
  let pL := schemeFieldBaseChangeToField (L := L) base
  let ev := fieldBaseChangeOpenPointCoordinateEvaluationLinearMap
    base M U I t xU hxU i
  let res := schemeModuleOpenSectionsRestrictionLinearMap pL ML
    (show V ≤ ⊤ from le_top)
  exact ev.comp (res.comp
    (schemeModuleGlobalSectionsLinearEquivOpenTop pL ML).toLinearMap)


/-- The linear coordinate evaluator has the same pointwise value as
the previously constructed field-point coordinate function. -/
theorem fieldBaseChangeOpenPointCoordinateEvaluationLinearMap_apply
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (M : X.Modules) (U : X.Opens) [IsAffine (U : Scheme.{u})]
    (I : Type u) [Fintype I] [DecidableEq I]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (xU : Spec (.of L) ⟶ (U : Scheme.{u}))
    (hxU : xU ≫ (U.ι ≫ base) =
      Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (i : I)
    (s : let g := schemeFieldBaseChangeToOriginal (L := L) base
      let V := g ⁻¹ᵁ U
      let ML := (Scheme.Modules.pullback g).obj M
      SchemeModuleOpenSectionsOver
        (schemeFieldBaseChangeToField (L := L) base) ML V) :
    fieldBaseChangeOpenPointCoordinateEvaluationLinearMap
        base M U I t xU hxU i s =
      fieldBaseChangeOpenPointCoordinateEvaluation
        base M U I t xU hxU i s := by
  simp only [fieldBaseChangeOpenPointCoordinateEvaluationLinearMap,
    fieldBaseChangeOpenPointCoordinateEvaluation, LinearMap.comp_apply,
    LinearMap.proj_apply, fieldPointΓevaluationLinearMap_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The global coordinate functional evaluates a categorical global section
through its canonical restriction to the inverse-image open. -/
theorem fieldBaseChangeGlobalPointCoordinateEvaluationLinearMap_apply
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (M : X.Modules) (U : X.Opens) [IsAffine (U : Scheme.{u})]
    (I : Type u) [Fintype I] [DecidableEq I]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (xU : Spec (.of L) ⟶ (U : Scheme.{u}))
    (hxU : xU ≫ (U.ι ≫ base) =
      Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (i : I)
    (σ : let g := schemeFieldBaseChangeToOriginal (L := L) base
      ((Scheme.Modules.pullback g).obj M).sections) :
    let g := schemeFieldBaseChangeToOriginal (L := L) base
    let V := g ⁻¹ᵁ U
    let ML := (Scheme.Modules.pullback g).obj M
    let pL := schemeFieldBaseChangeToField (L := L) base
    fieldBaseChangeGlobalPointCoordinateEvaluationLinearMap
        base M U I t xU hxU i
        ((schemeModuleGlobalSectionsOverEquivSections pL ML).symm σ) =
      fieldBaseChangeOpenPointCoordinateEvaluationLinearMap
        base M U I t xU hxU i
        (moduleRestrictTopLinearEquivOpenSectionsOver pL ML V
          (schemeModuleSectionsEquivTop (ML.restrict V.ι)
            (restrictModuleSection V.ι ML σ))) := by
  dsimp only
  let g := schemeFieldBaseChangeToOriginal (L := L) base
  let V := g ⁻¹ᵁ U
  let ML := (Scheme.Modules.pullback g).obj M
  let pL := schemeFieldBaseChangeToField (L := L) base
  let ev := fieldBaseChangeOpenPointCoordinateEvaluationLinearMap
    base M U I t xU hxU i
  unfold fieldBaseChangeGlobalPointCoordinateEvaluationLinearMap
  rw [← globalSectionOpenLinearEvaluation_apply pL ML V ev σ]


end

end PfaffianDescent
