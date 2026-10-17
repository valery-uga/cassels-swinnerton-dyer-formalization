import PfaffianDescent.VoisinGenericPullbackCoordinates

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u


noncomputable section

set_option backward.isDefEq.respectTransparency false in
/-- Restricting a categorical global section to the top open agrees with
the standard equivalence between sections and their value on the top open. -/
theorem module_open_top_globalSection
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules) (σ : M.sections) :
    (moduleRestrictTopLinearEquivOpenSectionsOver base M ⊤).symm
        (schemeModuleSectionsEquivTop M σ) =
      schemeModuleSectionsEquivTop (M.restrict (⊤ : X.Opens).ι)
        (BundleSectionZeroLocus.restrictModuleSection (⊤ : X.Opens).ι M σ) := by
  let q := moduleRestrictTopLinearEquivOpenSectionsOver base M ⊤
  change q.symm (schemeModuleSectionsEquivTop M σ) =
    (BundleSectionZeroLocus.restrictModuleSection
      (⊤ : X.Opens).ι M σ).val (Opposite.op ⊤)
  unfold BundleSectionZeroLocus.restrictModuleSection
  rw [SheafOfModules.unitHomEquiv_apply_coe]
  erw [ConcreteCategory.comp_apply]
  have hone :
      (ConcreteCategory.hom
        ((Scheme.Modules.restrictUnitIso (⊤ : X.Opens).ι).symm.hom.val.app
          (Opposite.op (⊤ : ((⊤ : X.Opens) : Scheme.{u}).Opens)))
          (1 : Γ(((⊤ : X.Opens) : Scheme.{u}), ⊤))) =
        (1 : Γ(X, (⊤ : X.Opens).ι ''ᵁ
          (⊤ : ((⊤ : X.Opens) : Scheme.{u}).Opens))) := by
    change (((⊤ : X.Opens).ι.appIso ⊤).inv.hom 1) = 1
    exact map_one _
  rw [hone]
  have hφ (τ : M.sections) :
      (ConcreteCategory.hom
        (((Scheme.Modules.restrictFunctor (⊤ : X.Opens).ι).map
          (M.unitHomEquiv.symm τ)).val.app
          (Opposite.op (⊤ : ((⊤ : X.Opens) : Scheme.{u}).Opens)))
        (1 : Γ(X, (⊤ : X.Opens).ι ''ᵁ
          (⊤ : ((⊤ : X.Opens) : Scheme.{u}).Opens)))) =
      τ.val (Opposite.op ((⊤ : X.Opens).ι ''ᵁ
        (⊤ : ((⊤ : X.Opens) : Scheme.{u}).Opens))) := by
    change ((M.unitHomEquiv.symm τ).val.app (Opposite.op
      ((⊤ : X.Opens).ι ''ᵁ
        (⊤ : ((⊤ : X.Opens) : Scheme.{u}).Opens)))).hom
      (1 : Γ(X, (⊤ : X.Opens).ι ''ᵁ
        (⊤ : ((⊤ : X.Opens) : Scheme.{u}).Opens))) = _
    rw [← SheafOfModules.unitHomEquiv_apply_coe]
    exact congrArg (fun z => z.val (Opposite.op
      ((⊤ : X.Opens).ι ''ᵁ
        (⊤ : ((⊤ : X.Opens) : Scheme.{u}).Opens))))
      (M.unitHomEquiv.apply_symm_apply τ)
  rw [hφ]
  dsimp only [q]
  unfold moduleRestrictTopLinearEquivOpenSectionsOver
  dsimp only
  simp only [Iso.trans_hom]
  dsimp only [Scheme.Modules.restrictAppIso]
  simp only [Functor.comp_obj]
  exact σ.property _

theorem module_coordinate_postcompose
    {X : Scheme.{u}} (I : Type u) [Fintype I] [DecidableEq I]
    {M N : X.Modules}
    (e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ M)
    (a : M ≅ N) (s : Γ(M, ⊤)) (i : I) :
    moduleOpenTopLinearEquivOfFreeIso I N (e ≪≫ a)
        ((a.hom.val.app (Opposite.op ⊤)).hom s) i =
      moduleOpenTopLinearEquivOfFreeIso I M e s i := by
  change (freeModuleOpenTopLinearEquiv I)
      ((e.inv.val.app (Opposite.op ⊤)).hom
        ((a.inv.val.app (Opposite.op ⊤)).hom
          ((a.hom.val.app (Opposite.op ⊤)).hom s))) i =
    (freeModuleOpenTopLinearEquiv I)
      ((e.inv.val.app (Opposite.op ⊤)).hom s) i
  have h := congrArg
    (fun q : M ⟶ M => (q.val.app (Opposite.op ⊤)).hom s)
    a.hom_inv_id
  have h' : (a.inv.val.app (Opposite.op ⊤)).hom
      ((a.hom.val.app (Opposite.op ⊤)).hom s) = s :=
    h.trans (ModuleCat.id_apply _ _)
  rw [h']

theorem module_iso_naturality_apply
    {X : Scheme.{u}} {M N : X.Modules} (a : M ≅ N)
    {P Q : X.Opens} (f : Opposite.op P ⟶ Opposite.op Q)
    (s : Γ(M, P)) :
    (a.hom.val.app (Opposite.op Q)).hom ((M.presheaf.map f).hom s) =
      (N.presheaf.map f).hom
        ((a.hom.val.app (Opposite.op P)).hom s) := by
  exact ConcreteCategory.congr_hom (a.hom.val.naturality f) s

/-- Restriction of ambient-open sections can be computed by restricting the
corresponding top-open section on the larger open subscheme. -/
theorem module_nested_open_restriction
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    {U W : X.Opens} (hWU : W ≤ U)
    (s : SchemeModuleOpenSectionsOver base M U) :
    let OW : Over U := Over.mk (homOfLE hWU)
    let UW : (U : Scheme.{u}).Opens :=
      U.overEquivalence.functor.obj OW
    let hUW : U.ι ''ᵁ UW = W := by
      change U.ι ''ᵁ (U.ι ⁻¹ᵁ W) = W
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
        Scheme.Opens.opensRange_ι, inf_eq_right.mpr hWU]
    let b : Γ(M.restrict U.ι, UW) ≅ Γ(M, W) :=
      M.restrictAppIso U.ι UW ≪≫
        M.presheaf.mapIso (eqToIso hUW.symm).op
    let qU := moduleRestrictTopLinearEquivOpenSectionsOver base M U
    let rUW : Opposite.op (⊤ : (U : Scheme.{u}).Opens) ⟶
        Opposite.op UW :=
      (homOfLE (show UW ≤ ⊤ from le_top)).op
    schemeModuleOpenSectionsRestrictionLinearMap base M hWU s =
      b.hom (((M.restrict U.ι).presheaf.map rUW).hom (qU.symm s)) := by
  dsimp only
  have hq :
      (moduleRestrictTopLinearEquivOpenSectionsOver base M U).symm s =
        (M.restrictAppIso U.ι ⊤ ≪≫
          M.presheaf.mapIso (eqToIso U.ι_image_top.symm).op).inv s := rfl
  rw [hq]
  unfold schemeModuleOpenSectionsRestrictionLinearMap
  dsimp only
  simp only [Iso.trans_hom, Iso.trans_inv, ConcreteCategory.comp_apply]
  erw [Scheme.Modules.map_restrictAppIso_hom_apply]
  erw [ConcreteCategory.comp_apply]
  erw [Iso.inv_hom_id_apply]
  let e0 : Opposite.op U ⟶
      Opposite.op (U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens)) :=
    (eqToIso U.ι_image_top.symm).op.inv
  let e1 : Opposite.op (U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens)) ⟶
      Opposite.op (U.ι ''ᵁ
        (U.overEquivalence.functor.obj (Over.mk (homOfLE hWU)))) :=
    (homOfLE (Scheme.Hom.image_mono U.ι
      (show U.ι ⁻¹ᵁ W ≤ ⊤ from le_top))).op
  let hUW : U.ι ''ᵁ
      (U.overEquivalence.functor.obj (Over.mk (homOfLE hWU))) = W := by
    change U.ι ''ᵁ (U.ι ⁻¹ᵁ W) = W
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, inf_eq_right.mpr hWU]
  let e2 : Opposite.op (U.ι ''ᵁ
      (U.overEquivalence.functor.obj (Over.mk (homOfLE hWU)))) ⟶
      Opposite.op W := (eqToIso hUW.symm).op.hom
  change (M.presheaf.map (homOfLE hWU).op).hom s =
    (M.presheaf.map e2).hom
      ((M.presheaf.map e1).hom ((M.presheaf.map e0).hom s))
  erw [← PresheafOfModules.map_comp_apply M.val e0 e1 s]
  erw [← PresheafOfModules.map_comp_apply M.val (e0 ≫ e1) e2 s]
  have he : (homOfLE hWU).op = (e0 ≫ e1) ≫ e2 :=
    Subsingleton.elim _ _
  rw [he]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of an ambient-open section agrees with restriction of the
corresponding categorical section on the larger open subscheme. -/
theorem module_open_restriction_as_restrictModuleSection
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    {U W : X.Opens} (hWU : W ≤ U)
    (s : SchemeModuleOpenSectionsOver base M U) :
    let h := X.homOfLE hWU
    let E := M.restrict U.ι
    let qU := moduleRestrictTopLinearEquivOpenSectionsOver base M U
    let qW := moduleRestrictTopLinearEquivOpenSectionsOver base M W
    let a := ((Scheme.Modules.restrictFunctorComp h U.ι).app M).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr
        (Scheme.homOfLE_ι X hWU)).app M
    qW.symm (schemeModuleOpenSectionsRestrictionLinearMap base M hWU s) =
      schemeModuleSectionsEquivTop (M.restrict W.ι)
        (SheafOfModules.sectionsMap a.hom
          (BundleSectionZeroLocus.restrictModuleSection h E
            ((schemeModuleSectionsEquivTop E).symm (qU.symm s)))) := by
  dsimp only
  let qW := moduleRestrictTopLinearEquivOpenSectionsOver base M W
  apply qW.injective
  rw [qW.apply_symm_apply]
  unfold schemeModuleOpenSectionsRestrictionLinearMap
  dsimp only [qW]
  unfold moduleRestrictTopLinearEquivOpenSectionsOver
  dsimp only
  unfold schemeModuleSectionsEquivTop
  unfold SheafOfModules.sectionsMap
  dsimp only
  simp only [Iso.trans_hom]
  dsimp only [Scheme.Modules.restrictAppIso]
  simp
  unfold BundleSectionZeroLocus.restrictModuleSection
  rw [SheafOfModules.unitHomEquiv_apply_coe]
  erw [ConcreteCategory.comp_apply]
  have hc := Scheme.Modules.restrictFunctorComp_inv_app_app
    (f := X.homOfLE hWU) (g := U.ι)
    (U := (⊤ : (W : Scheme.{u}).Opens)) M
  have he := Scheme.Modules.restrictFunctorCongr_hom_app_app
    (hf := Scheme.homOfLE_ι X hWU)
    (U := (⊤ : (W : Scheme.{u}).Opens)) M
  change _ = (M.presheaf.map _).hom
    ((Scheme.Modules.Hom.app
      ((Scheme.Modules.restrictFunctorCongr
        (Scheme.homOfLE_ι X hWU)).hom.app M) ⊤).hom
      ((Scheme.Modules.Hom.app
        ((Scheme.Modules.restrictFunctorComp
          (X.homOfLE hWU) U.ι).inv.app M) ⊤).hom
        _))
  rw [hc, he]
  erw [ConcreteCategory.comp_apply]
  have hone :
      (ConcreteCategory.hom
        ((Scheme.Modules.restrictUnitIso (X.homOfLE hWU)).symm.hom.val.app
          (Opposite.op (⊤ : (W : Scheme.{u}).Opens)))
          (1 : Γ((W : Scheme.{u}), ⊤))) =
        (1 : Γ((U : Scheme.{u}),
          (X.homOfLE hWU) ''ᵁ (⊤ : (W : Scheme.{u}).Opens))) := by
    change ((X.homOfLE hWU).appIso ⊤).inv.hom 1 = 1
    exact map_one _
  rw [hone]
  have hφ (τ : (M.restrict U.ι).sections) :
      (ConcreteCategory.hom
        (((Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map
          ((M.restrict U.ι).unitHomEquiv.symm τ)).val.app
          (Opposite.op (⊤ : (W : Scheme.{u}).Opens))))
        (1 : Γ((U : Scheme.{u}),
          (X.homOfLE hWU) ''ᵁ (⊤ : (W : Scheme.{u}).Opens))) =
      τ.val (Opposite.op
        ((X.homOfLE hWU) ''ᵁ (⊤ : (W : Scheme.{u}).Opens))) := by
    change (((M.restrict U.ι).unitHomEquiv.symm τ).val.app (Opposite.op
      ((X.homOfLE hWU) ''ᵁ (⊤ : (W : Scheme.{u}).Opens)))).hom
        (1 : Γ((U : Scheme.{u}),
          (X.homOfLE hWU) ''ᵁ (⊤ : (W : Scheme.{u}).Opens))) = _
    rw [← SheafOfModules.unitHomEquiv_apply_coe]
    exact congrArg (fun q => q.val (Opposite.op
      ((X.homOfLE hWU) ''ᵁ (⊤ : (W : Scheme.{u}).Opens))))
        ((M.restrict U.ι).unitHomEquiv.apply_symm_apply τ)
  erw [hφ]
  simp only [PresheafOfModules.sectionsMk]
  rw [Scheme.Modules.restrict_map]
  have collapse {A B C : X.Opensᵒᵖ} (f : A ⟶ B) (g : B ⟶ C)
      (x : M.presheaf.obj A) :
      (M.presheaf.map g).hom ((M.presheaf.map f).hom x) =
        (M.presheaf.map (f ≫ g)).hom x :=
    (PresheafOfModules.map_comp_apply M.val f g x).symm
  repeat' erw [collapse]
  have thin_map {A B : X.Opensᵒᵖ} (f g : A ⟶ B)
      (x : M.presheaf.obj A) :
      (M.presheaf.map f).hom x = (M.presheaf.map g).hom x := by
    rw [Subsingleton.elim f g]
  exact thin_map _ _ s

/-- Restriction of an ambient-open section is the canonical pullback along
the inclusion of the smaller open, transported through the standard module
comparison isomorphism. -/
theorem module_open_restriction_as_pullbackSection
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    {U W : X.Opens} (hWU : W ≤ U)
    (s : SchemeModuleOpenSectionsOver base M U) :
    let h := X.homOfLE hWU
    let E := M.restrict U.ι
    let qU := moduleRestrictTopLinearEquivOpenSectionsOver base M U
    let qW := moduleRestrictTopLinearEquivOpenSectionsOver base M W
    let r := nestedOpenRestrictionPullbackIso M hWU
    qW.symm (schemeModuleOpenSectionsRestrictionLinearMap base M hWU s) =
      schemeModuleSectionsEquivTop (M.restrict W.ι)
        (SheafOfModules.sectionsMap r.hom
          (BundleSectionZeroLocus.pullbackSection h E
            (BundleSectionZeroLocus.isIso_pullbackUnitComparison h)
            ((schemeModuleSectionsEquivTop E).symm (qU.symm s)))) := by
  dsimp only
  let h := X.homOfLE hWU
  let E := M.restrict U.ι
  let qU := moduleRestrictTopLinearEquivOpenSectionsOver base M U
  let qW := moduleRestrictTopLinearEquivOpenSectionsOver base M W
  let a := ((Scheme.Modules.restrictFunctorComp h U.ι).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr
      (Scheme.homOfLE_ι X hWU)).app M
  let σ := (schemeModuleSectionsEquivTop E).symm (qU.symm s)
  rw [module_open_restriction_as_restrictModuleSection base M hWU s]
  exact congrArg (schemeModuleSectionsEquivTop (M.restrict W.ι))
    (BundleSectionZeroLocus.sectionsMap_restrictModuleSection_eq_pullbackSection
      h (BundleSectionZeroLocus.isIso_pullbackUnitComparison h) a σ)

/-- The intrinsic local pullback of an ambient-open module section. -/
noncomputable def schemeFieldBaseChangeOpenPullbackSection
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (M : X.Modules) (U : X.Opens)
    (s : SchemeModuleOpenSectionsOver base M U) :
    let g := schemeFieldBaseChangeToOriginal (L := L) base
    let V := g ⁻¹ᵁ U
    let ML := (Scheme.Modules.pullback g).obj M
    SchemeModuleOpenSectionsOver
      (schemeFieldBaseChangeToField (L := L) base) ML V := by
  let g := schemeFieldBaseChangeToOriginal (L := L) base
  let V := g ⁻¹ᵁ U
  let ML := (Scheme.Modules.pullback g).obj M
  let pU := g ∣_ U
  let qU := moduleRestrictTopLinearEquivOpenSectionsOver base M U
  let qV := moduleRestrictTopLinearEquivOpenSectionsOver
    (schemeFieldBaseChangeToField (L := L) base) ML V
  exact qV (schemeModuleSectionsEquivTop (ML.restrict V.ι)
    (SheafOfModules.sectionsMap
      (schemeFieldBaseChangeOpenModuleIso base M U).hom
      (BundleSectionZeroLocus.pullbackSection pU (M.restrict U.ι)
        (BundleSectionZeroLocus.isIso_pullbackUnitComparison pU)
        ((schemeModuleSectionsEquivTop (M.restrict U.ι)).symm (qU.symm s)))))

/-- Canonical pullback of a module section commutes with restriction between
two inverse-image opens. -/
theorem pullbackSection_open_restriction_naturality
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) (M : X.Modules)
    {U W : X.Opens} (hWU : W ≤ U)
    (s : (M.restrict U.ι).sections) :
    let g := schemeFieldBaseChangeToOriginal (L := L) base
    let ML := (Scheme.Modules.pullback g).obj M
    let hK := X.homOfLE hWU
    let hL := (schemeFieldBaseChange base).homOfLE (g.preimage_mono hWU)
    let pW := g ∣_ W
    let pU := g ∣_ U
    let rK := nestedOpenRestrictionPullbackIso M hWU
    let rL := nestedOpenRestrictionPullbackIso ML (g.preimage_mono hWU)
    let AU := schemeFieldBaseChangeOpenModuleIso (K := K) (L := L) base M U
    let AW := schemeFieldBaseChangeOpenModuleIso (K := K) (L := L) base M W
    SheafOfModules.sectionsMap AW.hom
        (BundleSectionZeroLocus.pullbackSection pW (M.restrict W.ι)
          (BundleSectionZeroLocus.isIso_pullbackUnitComparison pW)
          (SheafOfModules.sectionsMap rK.hom
            (BundleSectionZeroLocus.pullbackSection hK (M.restrict U.ι)
              (BundleSectionZeroLocus.isIso_pullbackUnitComparison hK) s))) =
      SheafOfModules.sectionsMap rL.hom
        (BundleSectionZeroLocus.pullbackSection hL
          (ML.restrict (g ⁻¹ᵁ U).ι)
          (BundleSectionZeroLocus.isIso_pullbackUnitComparison hL)
          (SheafOfModules.sectionsMap AU.hom
            (BundleSectionZeroLocus.pullbackSection pU (M.restrict U.ι)
              (BundleSectionZeroLocus.isIso_pullbackUnitComparison pU) s))) := by
  dsimp only
  let g := schemeFieldBaseChangeToOriginal (L := L) base
  let ML := (Scheme.Modules.pullback g).obj M
  let hK := X.homOfLE hWU
  let hL := (schemeFieldBaseChange base).homOfLE (g.preimage_mono hWU)
  let pW := g ∣_ W
  let pU := g ∣_ U
  let E := M.restrict U.ι
  let rK := nestedOpenRestrictionPullbackIso M hWU
  let rL := nestedOpenRestrictionPullbackIso ML (g.preimage_mono hWU)
  let AU := schemeFieldBaseChangeOpenModuleIso (K := K) (L := L) base M U
  let AW := schemeFieldBaseChangeOpenModuleIso (K := K) (L := L) base M W
  let square := ((Scheme.Modules.pullbackComp pW hK).app E ≪≫
      (Scheme.Modules.pullbackCongr
        (morphismRestrict_homOfLE g W U hWU)).app E) ≪≫
    ((Scheme.Modules.pullbackComp hL pU).app E).symm
  let rLeft := BundleSectionZeroLocus.pullbackSection pW
    ((Scheme.Modules.pullback hK).obj E)
    (BundleSectionZeroLocus.isIso_pullbackUnitComparison pW)
    (BundleSectionZeroLocus.pullbackSection hK E
      (BundleSectionZeroLocus.isIso_pullbackUnitComparison hK) s)
  let rRight := BundleSectionZeroLocus.pullbackSection hL
    ((Scheme.Modules.pullback pU).obj E)
    (BundleSectionZeroLocus.isIso_pullbackUnitComparison hL)
    (BundleSectionZeroLocus.pullbackSection pU E
      (BundleSectionZeroLocus.isIso_pullbackUnitComparison pU) s)
  let Tleft := (Scheme.Modules.pullback pW).mapIso rK ≪≫ AW
  let Tright := (Scheme.Modules.pullback hL).mapIso AU ≪≫ rL
  have htransport := schemeFieldBaseChangeOpenModuleIso_naturality_restrict
    (K := K) (L := L) base M hWU
  have hsquare : SheafOfModules.sectionsMap square.hom rLeft = rRight := by
    exact BundleSectionZeroLocus.sectionsMap_pullbackSquare_pullbackSection
      pW hK hL pU (morphismRestrict_homOfLE g W U hWU) E
      (BundleSectionZeroLocus.isIso_pullbackUnitComparison pW)
      (BundleSectionZeroLocus.isIso_pullbackUnitComparison hK)
      (BundleSectionZeroLocus.isIso_pullbackUnitComparison (pW ≫ hK))
      (BundleSectionZeroLocus.isIso_pullbackUnitComparison hL)
      (BundleSectionZeroLocus.isIso_pullbackUnitComparison pU)
      (BundleSectionZeroLocus.isIso_pullbackUnitComparison (hL ≫ pU)) s
  calc
    SheafOfModules.sectionsMap AW.hom
        (BundleSectionZeroLocus.pullbackSection pW (M.restrict W.ι)
          (BundleSectionZeroLocus.isIso_pullbackUnitComparison pW)
          (SheafOfModules.sectionsMap rK.hom
            (BundleSectionZeroLocus.pullbackSection hK E
              (BundleSectionZeroLocus.isIso_pullbackUnitComparison hK) s))) =
      SheafOfModules.sectionsMap AW.hom
        (SheafOfModules.sectionsMap
          ((Scheme.Modules.pullback pW).map rK.hom) rLeft) :=
        congrArg (SheafOfModules.sectionsMap AW.hom)
          (BundleSectionZeroLocus.sectionsMap_pullbackSection pW rK.hom
            (BundleSectionZeroLocus.isIso_pullbackUnitComparison pW)
            (BundleSectionZeroLocus.pullbackSection hK E
              (BundleSectionZeroLocus.isIso_pullbackUnitComparison hK) s)).symm
    _ = SheafOfModules.sectionsMap Tleft.hom rLeft :=
      (SheafOfModules.sectionsMap_comp
        ((Scheme.Modules.pullback pW).map rK.hom) AW.hom rLeft).symm
    _ = SheafOfModules.sectionsMap (square ≪≫ Tright).hom rLeft := by
      rw [← htransport]
    _ = SheafOfModules.sectionsMap Tright.hom
        (SheafOfModules.sectionsMap square.hom rLeft) :=
      SheafOfModules.sectionsMap_comp square.hom Tright.hom rLeft
    _ = SheafOfModules.sectionsMap Tright.hom rRight :=
      congrArg (SheafOfModules.sectionsMap Tright.hom) hsquare
    _ = SheafOfModules.sectionsMap rL.hom
        (SheafOfModules.sectionsMap
          ((Scheme.Modules.pullback hL).map AU.hom) rRight) :=
      SheafOfModules.sectionsMap_comp
        ((Scheme.Modules.pullback hL).map AU.hom) rL.hom rRight
    _ = SheafOfModules.sectionsMap rL.hom
        (BundleSectionZeroLocus.pullbackSection hL
          (ML.restrict (g ⁻¹ᵁ U).ι)
          (BundleSectionZeroLocus.isIso_pullbackUnitComparison hL)
          (SheafOfModules.sectionsMap AU.hom
            (BundleSectionZeroLocus.pullbackSection pU E
              (BundleSectionZeroLocus.isIso_pullbackUnitComparison pU) s))) :=
      congrArg (SheafOfModules.sectionsMap rL.hom)
        (BundleSectionZeroLocus.sectionsMap_pullbackSection hL AU.hom
          (BundleSectionZeroLocus.isIso_pullbackUnitComparison hL)
          (BundleSectionZeroLocus.pullbackSection pU E
            (BundleSectionZeroLocus.isIso_pullbackUnitComparison pU) s))

set_option backward.isDefEq.respectTransparency false in
/-- Intrinsic pullback of ambient-open module sections along a field base
change commutes with restriction between inverse-image opens. -/
theorem schemeFieldBaseChangeOpenPullbackSection_restrict
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) (M : X.Modules)
    {U W : X.Opens} (hWU : W ≤ U)
    (s : SchemeModuleOpenSectionsOver base M U) :
    let g := schemeFieldBaseChangeToOriginal (L := L) base
    let ML := (Scheme.Modules.pullback g).obj M
    schemeModuleOpenSectionsRestrictionLinearMap
        (schemeFieldBaseChangeToField (L := L) base) ML
        (g.preimage_mono hWU)
        (schemeFieldBaseChangeOpenPullbackSection (L := L) base M U s) =
      schemeFieldBaseChangeOpenPullbackSection (L := L) base M W
        (schemeModuleOpenSectionsRestrictionLinearMap base M hWU s) := by
  dsimp only
  let g := schemeFieldBaseChangeToOriginal (L := L) base
  let ML := (Scheme.Modules.pullback g).obj M
  let VU := g ⁻¹ᵁ U
  let VW := g ⁻¹ᵁ W
  let pL := schemeFieldBaseChangeToField (L := L) base
  let qVW := moduleRestrictTopLinearEquivOpenSectionsOver pL ML VW
  apply qVW.symm.injective
  rw [module_open_restriction_as_pullbackSection pL ML
    (g.preimage_mono hWU)
    (schemeFieldBaseChangeOpenPullbackSection (L := L) base M U s)]
  unfold schemeFieldBaseChangeOpenPullbackSection
  dsimp only
  erw [(moduleRestrictTopLinearEquivOpenSectionsOver pL ML VU).symm_apply_apply]
  erw [qVW.symm_apply_apply]
  erw [(schemeModuleSectionsEquivTop (ML.restrict VU.ι)).symm_apply_apply]
  rw [module_open_restriction_as_pullbackSection base M hWU s]
  erw [(schemeModuleSectionsEquivTop (M.restrict W.ι)).symm_apply_apply]
  exact congrArg (schemeModuleSectionsEquivTop (ML.restrict VW.ι))
    (pullbackSection_open_restriction_naturality (L := L) base M hWU
      ((schemeModuleSectionsEquivTop (M.restrict U.ι)).symm
        ((moduleRestrictTopLinearEquivOpenSectionsOver base M U).symm s))).symm

theorem schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv_tmul_eq_smul_pullback
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (M : X.Modules) (U : X.Opens) [IsAffine (U : Scheme.{u})]
    (I : Type u) [Fintype I] [DecidableEq I]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (c : L) (s : SchemeModuleOpenSectionsOver base M U) :
    schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv
        base M U I t (c ⊗ₜ[K] s) =
      c • schemeFieldBaseChangeOpenPullbackSection
        (L := L) base M U s := by
  let g := schemeFieldBaseChangeToOriginal (L := L) base
  let V := g ⁻¹ᵁ U
  let ML := (Scheme.Modules.pullback g).obj M
  let pU := g ∣_ U
  let pV := V.ι ≫ schemeFieldBaseChangeToField (L := L) base
  let eU := BundleSectionZeroLocus.localFreeIsoOfOver U I t ≪≫
    (Scheme.Modules.overFunctorEquiv U).app M
  let eV := schemeFieldBaseChangeOpenRestrictedFreeIso
    (K := K) (L := L) base M U I t
  let AU := schemeFieldBaseChangeOpenModuleIso
    (K := K) (L := L) base M U
  let qU := moduleRestrictTopLinearEquivOpenSectionsOver base M U
  let qV := moduleRestrictTopLinearEquivOpenSectionsOver
    (schemeFieldBaseChangeToField (L := L) base) ML V
  letI := Module.compHom Γ((V : Scheme.{u}), ⊤)
    (schemeOpenBaseRingHom pV ⊤)
  apply qV.symm.injective
  let coordV := moduleOpenTopLinearEquivOfFreeIsoOver pV I
    (ML.restrict V.ι) eV
  apply coordV.injective
  funext i
  rw [schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv_tmul_coord]
  symm
  change coordV (qV.symm (c •
    schemeFieldBaseChangeOpenPullbackSection (L := L) base M U s)) i = _
  rw [map_smul, map_smul]
  unfold schemeFieldBaseChangeOpenPullbackSection
  dsimp only [qV, ML, V, g]
  erw [qV.symm_apply_apply]
  let p := BundleSectionZeroLocus.pullbackSection pU (M.restrict U.ι)
    (BundleSectionZeroLocus.isIso_pullbackUnitComparison pU)
    ((schemeModuleSectionsEquivTop (M.restrict U.ι)).symm (qU.symm s))
  let coord0 := moduleOpenTopLinearEquivOfFreeIso I
    (ML.restrict V.ι)
      (BundleSectionZeroLocus.pullbackFreeIso pU I eU ≪≫ AU)
  have hcoord0 (x : Γ(ML.restrict V.ι, ⊤)) :
      coordV x i = coord0 x i := rfl
  simp only [Pi.smul_apply]
  erw [hcoord0]
  have hpost := module_coordinate_postcompose I
    (BundleSectionZeroLocus.pullbackFreeIso pU I eU) AU
    (schemeModuleSectionsEquivTop _ p) i
  dsimp only [coord0]
  have hsec :
      schemeModuleSectionsEquivTop (ML.restrict V.ι)
          (SheafOfModules.sectionsMap AU.hom p) =
        (AU.hom.val.app (Opposite.op ⊤)).hom
          (schemeModuleSectionsEquivTop _ p) := rfl
  erw [hsec]
  rw [hpost]
  rw [BundleSectionZeroLocus.moduleOpenTopLinearEquivOfPullbackFreeIso_general pU I
    (M.restrict U.ι) eU (qU.symm s) i]
  rw [schemeFieldBaseChangeOpenGlobalFunctionsLinearEquiv_tmul]
  rfl

/-- On a pure tensor, the local free-module base-change equivalences commute
with restriction to a smaller affine open. -/
theorem schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv_tmul_restrict
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) (M : X.Modules)
    {U W : X.Opens} (hWU : W ≤ U)
    [IsAffine (U : Scheme.{u})] [IsAffine (W : Scheme.{u})]
    (I : Type u) [Fintype I] [DecidableEq I]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (c : L) (s : SchemeModuleOpenSectionsOver base M U) :
    schemeModuleOpenSectionsRestrictionLinearMap
        (schemeFieldBaseChangeToField (L := L) base)
        ((Scheme.Modules.pullback
          (schemeFieldBaseChangeToOriginal (L := L) base)).obj M)
        ((schemeFieldBaseChangeToOriginal (L := L) base).preimage_mono hWU)
        (schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv
          base M U I t (c ⊗ₜ[K] s)) =
      schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv
        base M W I
          (BundleSectionZeroLocus.restrictFreeIsoOver
            (homOfLE hWU) I t)
          (c ⊗ₜ[K]
            schemeModuleOpenSectionsRestrictionLinearMap base M hWU s) := by
  dsimp only
  rw [schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv_tmul_eq_smul_pullback,
    schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv_tmul_eq_smul_pullback]
  rw [map_smul]
  congr 1
  exact schemeFieldBaseChangeOpenPullbackSection_restrict base M hWU s

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The local free-module base-change equivalences commute with restriction
on every tensor, by linear extension from the pure-tensor calculation. -/
theorem schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv_restrict
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) (M : X.Modules)
    {U W : X.Opens} (hWU : W ≤ U)
    [IsAffine (U : Scheme.{u})] [IsAffine (W : Scheme.{u})]
    (I : Type u) [Fintype I] [DecidableEq I]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (x : L ⊗[K] SchemeModuleOpenSectionsOver base M U) :
    schemeModuleOpenSectionsRestrictionLinearMap
        (schemeFieldBaseChangeToField (L := L) base)
        ((Scheme.Modules.pullback
          (schemeFieldBaseChangeToOriginal (L := L) base)).obj M)
        ((schemeFieldBaseChangeToOriginal (L := L) base).preimage_mono hWU)
        (schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv
          base M U I t x) =
      schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv
        base M W I
          (BundleSectionZeroLocus.restrictFreeIsoOver
            (homOfLE hWU) I t)
          (TensorProduct.AlgebraTensorModule.lTensor L L
            (schemeModuleOpenSectionsRestrictionLinearMap base M hWU) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c s =>
      have h :=
        @schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv_tmul_restrict
          K L _ _ _ X base M U W hWU _ _ I _ _ t c s
      rw [TensorProduct.AlgebraTensorModule.lTensor_tmul
        (schemeModuleOpenSectionsRestrictionLinearMap base M hWU) c s]
      rw [h]
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (fun a b => a + b) hx hy

/-- The local base-change equivalence is independent of the chosen finite
free presentation.  Both presentations compute the same canonical pullback
on pure tensors, and hence on every tensor. -/
theorem schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv_independent
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (base : X ⟶ Spec (.of K)) (M : X.Modules)
    (U : X.Opens) [IsAffine (U : Scheme.{u})]
    (I J : Type u)
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (tI : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (tJ : SheafOfModules.free (R := X.ringCatSheaf.over U) J ≅ M.over U)
    (x : L ⊗[K] SchemeModuleOpenSectionsOver base M U) :
    schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv
        base M U I tI x =
      schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv
        base M U J tJ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c s =>
      rw [schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv_tmul_eq_smul_pullback,
        schemeFieldBaseChangeOpenFreeModuleSectionsLinearEquiv_tmul_eq_smul_pullback]
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (fun a b => a + b) hx hy

end

end PfaffianDescent
