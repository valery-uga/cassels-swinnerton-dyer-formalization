import PfaffianDescent.VoisinFieldBaseChangeOpenCanonicalPullback

/-!
# Compatibility of open and global pullback under field base change

This file identifies the intrinsic pullback on an inverse-image open with
the restriction of the corresponding global pullback section.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory Opposite BundleSectionZeroLocus

universe u

noncomputable section

/-- Pulling back the restriction of a global section to an open gives the
restriction of its global pullback to the inverse-image open. -/
theorem schemeFieldBaseChangeOpenPullback_restricted_global
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (M : X.Modules) (U : X.Opens) (σ : M.sections) :
    let g := schemeFieldBaseChangeToOriginal (L := L) base
    let V := g ⁻¹ᵁ U
    let p := g ∣_ U
    let ML := (Scheme.Modules.pullback g).obj M
    SheafOfModules.sectionsMap
        (schemeFieldBaseChangeOpenModuleIso base M U).hom
        (BundleSectionZeroLocus.pullbackSection p (M.restrict U.ι)
          (BundleSectionZeroLocus.isIso_pullbackUnitComparison p)
          (BundleSectionZeroLocus.restrictModuleSection U.ι M σ)) =
      BundleSectionZeroLocus.restrictModuleSection V.ι ML
        (BundleSectionZeroLocus.pullbackSection g M
          (BundleSectionZeroLocus.isIso_pullbackUnitComparison g) σ) := by
  dsimp only
  let g := schemeFieldBaseChangeToOriginal (L := L) base
  let V := g ⁻¹ᵁ U
  let p := g ∣_ U
  let ML := (Scheme.Modules.pullback g).obj M
  let αU := (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M
  let αV := (Scheme.Modules.restrictFunctorIsoPullback V.ι).app ML
  let A := (Scheme.Modules.pullback p).mapIso αU
  let B := (Scheme.Modules.pullbackComp p U.ι).app M
  let C := (Scheme.Modules.pullbackCongr (morphismRestrict_ι g U)).app M
  let D := (Scheme.Modules.pullbackComp V.ι g).app M
  let rU := BundleSectionZeroLocus.restrictModuleSection U.ι M σ
  let sU := BundleSectionZeroLocus.pullbackSection p (M.restrict U.ι)
    (BundleSectionZeroLocus.isIso_pullbackUnitComparison p) rU
  let sV := BundleSectionZeroLocus.restrictModuleSection V.ι ML
    (BundleSectionZeroLocus.pullbackSection g M
      (BundleSectionZeroLocus.isIso_pullbackUnitComparison g) σ)
  have hinj : Function.Injective (SheafOfModules.sectionsMap αV.hom) := by
    intro x y hxy
    have h := congrArg (SheafOfModules.sectionsMap αV.inv) hxy
    exact (BundleSectionZeroLocus.sectionsMap_hom_inv αV.symm x).symm.trans
      (h.trans (BundleSectionZeroLocus.sectionsMap_hom_inv αV.symm y))
  apply hinj
  have hU : SheafOfModules.sectionsMap αU.hom rU =
      BundleSectionZeroLocus.pullbackSection U.ι M
        (BundleSectionZeroLocus.isIso_pullbackUnitComparison U.ι) σ :=
    BundleSectionZeroLocus.restrictModuleSection_to_pullbackSection U.ι
      (BundleSectionZeroLocus.isIso_pullbackUnitComparison U.ι) σ
  have hV : SheafOfModules.sectionsMap αV.hom sV =
      BundleSectionZeroLocus.pullbackSection V.ι ML
        (BundleSectionZeroLocus.isIso_pullbackUnitComparison V.ι)
        (BundleSectionZeroLocus.pullbackSection g M
          (BundleSectionZeroLocus.isIso_pullbackUnitComparison g) σ) :=
    BundleSectionZeroLocus.restrictModuleSection_to_pullbackSection V.ι
      (BundleSectionZeroLocus.isIso_pullbackUnitComparison V.ι)
      (BundleSectionZeroLocus.pullbackSection g M
        (BundleSectionZeroLocus.isIso_pullbackUnitComparison g) σ)
  rw [hV]
  let E := ((A ≪≫ B) ≪≫ C) ≪≫ D.symm
  have hcancel :
      SheafOfModules.sectionsMap αV.hom
          (SheafOfModules.sectionsMap (E ≪≫ αV.symm).hom sU) =
        SheafOfModules.sectionsMap E.hom sU := by
    calc
      _ = SheafOfModules.sectionsMap αV.hom
          (SheafOfModules.sectionsMap αV.inv
            (SheafOfModules.sectionsMap E.hom sU)) :=
        congrArg (SheafOfModules.sectionsMap αV.hom)
          (SheafOfModules.sectionsMap_comp E.hom αV.inv sU)
      _ = _ := BundleSectionZeroLocus.sectionsMap_hom_inv αV _
  change SheafOfModules.sectionsMap αV.hom
      (SheafOfModules.sectionsMap (E ≪≫ αV.symm).hom sU) = _
  refine hcancel.trans ?_
  have hA : SheafOfModules.sectionsMap A.hom sU =
      BundleSectionZeroLocus.pullbackSection p
        ((Scheme.Modules.pullback U.ι).obj M)
        (BundleSectionZeroLocus.isIso_pullbackUnitComparison p)
        (SheafOfModules.sectionsMap αU.hom rU) :=
    BundleSectionZeroLocus.sectionsMap_pullbackSection p αU.hom
      (BundleSectionZeroLocus.isIso_pullbackUnitComparison p) rU
  calc
    SheafOfModules.sectionsMap E.hom sU =
        SheafOfModules.sectionsMap (((B ≪≫ C) ≪≫ D.symm).hom)
          (SheafOfModules.sectionsMap A.hom sU) := by
      exact SheafOfModules.sectionsMap_comp A.hom
        (((B ≪≫ C) ≪≫ D.symm).hom) sU
    _ = SheafOfModules.sectionsMap (((B ≪≫ C) ≪≫ D.symm).hom)
        (BundleSectionZeroLocus.pullbackSection p
          ((Scheme.Modules.pullback U.ι).obj M)
          (BundleSectionZeroLocus.isIso_pullbackUnitComparison p)
          (SheafOfModules.sectionsMap αU.hom rU)) :=
      congrArg (SheafOfModules.sectionsMap (((B ≪≫ C) ≪≫ D.symm).hom)) hA
    _ = SheafOfModules.sectionsMap (((B ≪≫ C) ≪≫ D.symm).hom)
        (BundleSectionZeroLocus.pullbackSection p
          ((Scheme.Modules.pullback U.ι).obj M)
          (BundleSectionZeroLocus.isIso_pullbackUnitComparison p)
          (BundleSectionZeroLocus.pullbackSection U.ι M
            (BundleSectionZeroLocus.isIso_pullbackUnitComparison U.ι) σ)) :=
      congrArg (SheafOfModules.sectionsMap (((B ≪≫ C) ≪≫ D.symm).hom))
        (congrArg (BundleSectionZeroLocus.pullbackSection p
          ((Scheme.Modules.pullback U.ι).obj M)
          (BundleSectionZeroLocus.isIso_pullbackUnitComparison p)) hU)
    _ = _ := BundleSectionZeroLocus.sectionsMap_pullbackSquare_pullbackSection
      p U.ι V.ι g (morphismRestrict_ι g U) M
      (BundleSectionZeroLocus.isIso_pullbackUnitComparison p)
      (BundleSectionZeroLocus.isIso_pullbackUnitComparison U.ι)
      (BundleSectionZeroLocus.isIso_pullbackUnitComparison (p ≫ U.ι))
      (BundleSectionZeroLocus.isIso_pullbackUnitComparison V.ι)
      (BundleSectionZeroLocus.isIso_pullbackUnitComparison g)
      (BundleSectionZeroLocus.isIso_pullbackUnitComparison (V.ι ≫ g)) σ

/-- A global section recovered from its canonical restriction to the top
open is the original top-open section. -/
theorem module_topOpenSection_restricted_global
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules) (σ : M.sections) :
    moduleRestrictTopLinearEquivOpenSectionsOver base M ⊤
        (schemeModuleSectionsEquivTop (M.restrict (⊤ : X.Opens).ι)
          (BundleSectionZeroLocus.restrictModuleSection
            (⊤ : X.Opens).ι M σ)) =
      schemeModuleSectionsEquivTop M σ := by
  let q := moduleRestrictTopLinearEquivOpenSectionsOver base M ⊤
  have h := module_open_top_globalSection base M σ
  have h' := congrArg q h
  exact h'.symm.trans (q.apply_symm_apply _)

set_option backward.isDefEq.respectTransparency false in
/-- The intrinsic pullback of an open section obtained by restricting a
global section is the corresponding restricted global pullback section. -/
theorem schemeFieldBaseChangeOpenPullback_of_restricted_global
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (M : X.Modules) (U : X.Opens) (σ : M.sections) :
    let g := schemeFieldBaseChangeToOriginal (L := L) base
    let V := g ⁻¹ᵁ U
    let pL := schemeFieldBaseChangeToField (L := L) base
    let ML := (Scheme.Modules.pullback g).obj M
    let qU := moduleRestrictTopLinearEquivOpenSectionsOver base M U
    let qV := moduleRestrictTopLinearEquivOpenSectionsOver pL ML V
    schemeFieldBaseChangeOpenPullbackSection (L := L) base M U
        (qU (schemeModuleSectionsEquivTop (M.restrict U.ι)
          (BundleSectionZeroLocus.restrictModuleSection U.ι M σ))) =
      qV (schemeModuleSectionsEquivTop (ML.restrict V.ι)
        (BundleSectionZeroLocus.restrictModuleSection V.ι ML
          (BundleSectionZeroLocus.pullbackSection g M
            (BundleSectionZeroLocus.isIso_pullbackUnitComparison g) σ))) := by
  dsimp only
  let g := schemeFieldBaseChangeToOriginal (L := L) base
  let V := g ⁻¹ᵁ U
  let pL := schemeFieldBaseChangeToField (L := L) base
  let ML := (Scheme.Modules.pullback g).obj M
  let qU := moduleRestrictTopLinearEquivOpenSectionsOver base M U
  let qV := moduleRestrictTopLinearEquivOpenSectionsOver pL ML V
  let rU := BundleSectionZeroLocus.restrictModuleSection U.ι M σ
  let τ := BundleSectionZeroLocus.pullbackSection g M
    (BundleSectionZeroLocus.isIso_pullbackUnitComparison g) σ
  let rV := BundleSectionZeroLocus.restrictModuleSection V.ι ML τ
  have hp := schemeFieldBaseChangeOpenPullback_restricted_global
    (L := L) base M U σ
  unfold schemeFieldBaseChangeOpenPullbackSection
  dsimp only [qU, qV, rU, rV, τ, V, ML, pL, g]
  erw [(moduleRestrictTopLinearEquivOpenSectionsOver base M U).symm_apply_apply]
  erw [(schemeModuleSectionsEquivTop (M.restrict U.ι)).symm_apply_apply]
  rw [hp]

set_option backward.isDefEq.respectTransparency false in
/-- On the top open, intrinsic open pullback is exactly evaluation of the
canonical global pullback section. -/
theorem schemeFieldBaseChangeOpenPullback_top_global
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (M : X.Modules) (σ : M.sections) :
    schemeFieldBaseChangeOpenPullbackSection (L := L) base M ⊤
        (schemeModuleSectionsEquivTop M σ) =
      schemeModuleSectionsEquivTop
        ((Scheme.Modules.pullback
          (schemeFieldBaseChangeToOriginal (L := L) base)).obj M)
        (BundleSectionZeroLocus.pullbackSection
          (schemeFieldBaseChangeToOriginal (L := L) base) M
          (BundleSectionZeroLocus.isIso_pullbackUnitComparison
            (schemeFieldBaseChangeToOriginal (L := L) base)) σ) := by
  let g := schemeFieldBaseChangeToOriginal (L := L) base
  let pL := schemeFieldBaseChangeToField (L := L) base
  let ML := (Scheme.Modules.pullback g).obj M
  let τ := BundleSectionZeroLocus.pullbackSection g M
    (BundleSectionZeroLocus.isIso_pullbackUnitComparison g) σ
  rw [← module_topOpenSection_restricted_global base M σ]
  rw [schemeFieldBaseChangeOpenPullback_of_restricted_global]
  exact module_topOpenSection_restricted_global pL ML τ

end

end PfaffianDescent
