import PfaffianDescent.TargetAffineIdealKernel

/-! Extending the affine ideal-module comparison across a target chart. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

/-- Monicity of the lower arrow in an isomorphism square transports
to the middle arrow after applying any functor. -/
private theorem mono_map_middle_of_iso_square
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B C' D' : C} (e : A ≅ B) (c : C' ≅ D')
    (α : A ⟶ D') (b : B ⟶ C')
    (hs : e.hom ≫ b ≫ c.hom = α)
    (hα : Mono (F.map α)) : Mono (F.map b) := by
  have hs' : e.hom ≫ (b ≫ c.hom) = α := by
    simpa only [Category.assoc] using hs
  have heq : b = e.inv ≫ α ≫ c.inv := by
    simpa only [Category.assoc] using
      (c.eq_comp_inv).2 ((e.eq_inv_comp).2 hs')
  have he : Mono (F.map e.inv) := by
    have h := (F.mapIso e).inv_hom_id
    change F.map e.inv ≫ F.map e.hom = 𝟙 _ at h
    exact mono_of_mono_fac (f := F.map e.hom) h
  have hc : Mono (F.map c.inv) := by
    have h := (F.mapIso c).inv_hom_id
    change F.map c.inv ≫ F.map c.hom = 𝟙 _ at h
    exact mono_of_mono_fac (f := F.map c.hom) h
  have hm : Mono (F.map e.inv ≫ F.map α ≫ F.map c.inv) :=
    mono_comp' he (mono_comp' hα hc)
  have hmap : F.map (e.inv ≫ α ≫ c.inv) =
      F.map e.inv ≫ F.map α ≫ F.map c.inv := by
    simp only [Functor.map_comp]
  exact heq.symm ▸ hmap.symm ▸ hm

/-- The checked comparison of actual ideal-module sections defines a
natural transformation on the affine-open basis of a target chart. -/
noncomputable def targetAffineChartIdealModule_basisNatTrans
    {Y Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : Y.affineCover.I₀) :
    let U := Y.affineCover.X a
    let u := Y.affineCover.f a
    let iU := pullback.fst u i
    let B : U.affineOpens → Opens U := fun V => V.1
    (inducedFunctor B).op ⋙
      ((SheafOfModules.toSheaf U.ringCatSheaf).obj
        (IdealSheafDataModule.closedImmersionModule iU)).1 ⟶
    (inducedFunctor B).op ⋙
      ((SheafOfModules.toSheaf U.ringCatSheaf).obj
        ((Scheme.Modules.restrictFunctor u).obj
          (IdealSheafDataModule.closedImmersionModule i))).1 := by
  dsimp only
  refine { app := ?_, naturality := ?_ }
  · intro V
    exact AddCommGrpCat.ofHom
      (targetAffineChartIdealModule_sectionsAddEquiv i a V.unop).toAddMonoidHom
  · intro V W j
    ext m
    exact targetAffineChartIdealModule_sectionsEquiv_natural i a W.unop V.unop
      ((inducedFunctor (fun V : (Y.affineCover.X a).affineOpens => V.1)).op.map j) m

/-- The affine-basis comparison extends uniquely to an additive sheaf
morphism on the entire target chart. -/
noncomputable def targetAffineChartIdealModule_addSheafHom
    {Y Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : Y.affineCover.I₀) :
    let U := Y.affineCover.X a
    let u := Y.affineCover.f a
    let iU := pullback.fst u i
    (SheafOfModules.toSheaf U.ringCatSheaf).obj
      (IdealSheafDataModule.closedImmersionModule iU) ⟶
    (SheafOfModules.toSheaf U.ringCatSheaf).obj
      ((Scheme.Modules.restrictFunctor u).obj
        (IdealSheafDataModule.closedImmersionModule i)) := by
  dsimp only
  let U := Y.affineCover.X a
  let B : U.affineOpens → Opens U := fun V => V.1
  have hB : Opens.IsBasis (Set.range B) := by
    simpa [B] using U.isBasis_affineOpens
  exact ⟨TopCat.Sheaf.restrictHomEquivHom _ _ hB
    (targetAffineChartIdealModule_basisNatTrans i a)⟩

/-- The additive sheaf comparison is an isomorphism because it is an
isomorphism on every member of the affine-open basis. -/
theorem targetAffineChartIdealModule_addSheafHom_isIso
    {Y Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : Y.affineCover.I₀) :
    IsIso (targetAffineChartIdealModule_addSheafHom i a) := by
  let U := Y.affineCover.X a
  let B : U.affineOpens → Opens U := fun V => V.1
  have hB : Opens.IsBasis (Set.range B) := by
    simpa [B] using U.isBasis_affineOpens
  apply TopCat.Sheaf.isIso_iff_isIso_basis hB
  intro V
  change IsIso ((TopCat.Sheaf.restrictHomEquivHom _ _ hB
    (targetAffineChartIdealModule_basisNatTrans i a)).app
      (Opposite.op (B V)))
  have heq := TopCat.Sheaf.extend_hom_app _ _ hB
    (targetAffineChartIdealModule_basisNatTrans i a) V
  have hi : IsIso ((targetAffineChartIdealModule_basisNatTrans i a).app
      (Opposite.op V)) := by
    change IsIso
      ((targetAffineChartIdealModule_sectionsAddEquiv i a V).toAddCommGrpIso.hom)
    infer_instance
  exact heq.symm ▸ hi

/-- The actual ideal modules on a target chart are isomorphic as
underlying additive sheaves. -/
noncomputable def targetAffineChartIdealModule_addSheafIso
    {Y Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : Y.affineCover.I₀) :
    let U := Y.affineCover.X a
    let u := Y.affineCover.f a
    let iU := pullback.fst u i
    (SheafOfModules.toSheaf U.ringCatSheaf).obj
      (IdealSheafDataModule.closedImmersionModule iU) ≅
    (SheafOfModules.toSheaf U.ringCatSheaf).obj
      ((Scheme.Modules.restrictFunctor u).obj
        (IdealSheafDataModule.closedImmersionModule i)) := by
  letI := targetAffineChartIdealModule_addSheafHom_isIso i a
  exact asIso (targetAffineChartIdealModule_addSheafHom i a)

/-- On affine opens, the global additive sheaf comparison is the
explicit checked section equivalence. -/
theorem targetAffineChartIdealModule_addSheafHom_app_affine
    {Y Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : Y.affineCover.I₀)
    (V : (Y.affineCover.X a).affineOpens) :
    (targetAffineChartIdealModule_addSheafHom i a).hom.app
      (Opposite.op V.1) =
      AddCommGrpCat.ofHom
        (targetAffineChartIdealModule_sectionsAddEquiv i a V).toAddMonoidHom := by
  let U := Y.affineCover.X a
  let B : U.affineOpens → Opens U := fun V => V.1
  have hB : Opens.IsBasis (Set.range B) := by
    simpa [B] using U.isBasis_affineOpens
  exact TopCat.Sheaf.extend_hom_app _ _ hB
    (targetAffineChartIdealModule_basisNatTrans i a) V

/-- The additive sheaf comparison intertwines the actual ideal
inclusions into the structure sheaf. -/
theorem targetAffineChartIdealModule_addSheafHom_toUnit
    {Y Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : Y.affineCover.I₀) :
    let U := Y.affineCover.X a
    let u := Y.affineCover.f a
    let iU := pullback.fst u i
    let T := SheafOfModules.toSheaf U.ringCatSheaf
    targetAffineChartIdealModule_addSheafHom i a ≫
      T.map ((Scheme.Modules.restrictFunctor u).map
        (IdealSheafDataModule.closedImmersionModuleToUnit i)) ≫
      T.map (Scheme.Modules.restrictUnitIso u).hom =
      T.map (IdealSheafDataModule.closedImmersionModuleToUnit iU) := by
  dsimp only
  let U := Y.affineCover.X a
  let B : U.affineOpens → Opens U := fun V => V.1
  have hB : Opens.IsBasis (Set.range B) := by
    simpa [B] using U.isBasis_affineOpens
  apply CategoryTheory.Sheaf.hom_ext
  apply TopCat.Sheaf.hom_ext _ _ hB
  intro V
  ext m
  change ((Y.affineCover.f a).appIso V).hom.hom
      ((IdealSheafDataModule.closedImmersionModuleToUnit i).val.app
        (Opposite.op ((Y.affineCover.f a) ''ᵁ V.1))
        (((targetAffineChartIdealModule_addSheafHom i a).hom.app
          (Opposite.op V.1)) m)) =
      (IdealSheafDataModule.closedImmersionModuleToUnit
        (pullback.fst (Y.affineCover.f a) i)).val.app
          (Opposite.op V.1) m
  rw [targetAffineChartIdealModule_addSheafHom_app_affine]
  have h := targetAffineChartIdealModule_sectionsEquiv_toUnit i a V m
  have h' := congrArg ((Y.affineCover.f a).appIso V).hom.hom h
  change ((Y.affineCover.f a).appIso V).hom.hom
      ((IdealSheafDataModule.closedImmersionModuleToUnit i).val.app
        (Opposite.op ((Y.affineCover.f a) ''ᵁ V.1))
        (targetAffineChartIdealModule_sectionsEquiv i a V m)) =
      (IdealSheafDataModule.closedImmersionModuleToUnit
        (pullback.fst (Y.affineCover.f a) i)).val.app
          (Opposite.op V.1) m
  have hcomp (x : Γ(Y.affineCover.X a, V.1)) :
      ((Y.affineCover.f a).appIso V).hom.hom
        (((Y.affineCover.f a).appIso V).inv.hom x) = x := by
    have q := ConcreteCategory.congr_hom
      ((Y.affineCover.f a).appIso V).inv_hom_id x
    simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using q
  exact h'.symm.trans (hcomp _)

/-- A monomorphism of scheme modules is injective on sections over
every open set. -/
theorem schemeModule_mono_app_injective
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    [Mono f] (W : Opens X) :
    Function.Injective (f.val.app (Opposite.op W)) := by
  let E := SheafOfModules.evaluation X.ringCatSheaf (Opposite.op W)
  let hfin : PreservesFiniteLimits E := by infer_instance
  let hshape : PreservesLimitsOfShape WalkingCospan E :=
    hfin.preservesFiniteLimits WalkingCospan
  letI : PreservesLimit (cospan f f) E := hshape.preservesLimit
  have hf : Mono f := inferInstance
  have hmono : Mono (E.map f) :=
    @preserves_mono_of_preservesLimit _ _ _ _ E _ _ f inferInstance hf
  exact (ModuleCat.mono_iff_injective (E.map f)).mp hmono

/-- The additive comparison lifts to a morphism of actual ideal-module
sheaves, using the inclusion square to prove linearity on all opens. -/
noncomputable def targetAffineChartIdealModule_moduleHom
    {Y Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : Y.affineCover.I₀) :
    let U := Y.affineCover.X a
    let u := Y.affineCover.f a
    let iU := pullback.fst u i
    IdealSheafDataModule.closedImmersionModule iU ⟶
      (Scheme.Modules.restrictFunctor u).obj
        (IdealSheafDataModule.closedImmersionModule i) := by
  let U := Y.affineCover.X a
  let u := Y.affineCover.f a
  let iU := pullback.fst u i
  let M := IdealSheafDataModule.closedImmersionModule iU
  let N := (Scheme.Modules.restrictFunctor u).obj
    (IdealSheafDataModule.closedImmersionModule i)
  let α := IdealSheafDataModule.closedImmersionModuleToUnit iU
  let q : N ⟶ SheafOfModules.unit U.ringCatSheaf :=
    (Scheme.Modules.restrictFunctor u).map
      (IdealSheafDataModule.closedImmersionModuleToUnit i) ≫
        (Scheme.Modules.restrictUnitIso u).hom
  let T := SheafOfModules.toSheaf U.ringCatSheaf
  let φ := (targetAffineChartIdealModule_addSheafHom i a).hom
  haveI : IsOpenImmersion u := inferInstance
  have hq : Mono q := by
    have hβ : Mono (IdealSheafDataModule.closedImmersionModuleToUnit i) := by
      change Mono (IdealSheafDataModule.idealModuleToUnit i.ker)
      infer_instance
    haveI : Mono (IdealSheafDataModule.closedImmersionModuleToUnit i) := hβ
    have hrestr : Mono ((Scheme.Modules.restrictFunctor u).map
        (IdealSheafDataModule.closedImmersionModuleToUnit i)) :=
      @openImmersionRestrictFunctor_map_mono _ _ u inferInstance _ _
        (IdealSheafDataModule.closedImmersionModuleToUnit i) hβ
    have hunit : Mono (Scheme.Modules.restrictUnitIso u).hom :=
      mono_of_mono_fac (f := (Scheme.Modules.restrictUnitIso u).inv)
        (Scheme.Modules.restrictUnitIso u).hom_inv_id
    exact mono_comp' hrestr hunit
  have hs : targetAffineChartIdealModule_addSheafHom i a ≫ T.map q =
      T.map α := by
    let b := (Scheme.Modules.restrictFunctor u).map
      (IdealSheafDataModule.closedImmersionModuleToUnit i)
    let c := (Scheme.Modules.restrictUnitIso u).hom
    have hmap : T.map (b ≫ c) = T.map b ≫ T.map c := T.map_comp b c
    have hsq : targetAffineChartIdealModule_addSheafHom i a ≫
        (T.map b ≫ T.map c) = T.map α := by
      simpa only [Category.assoc] using
        targetAffineChartIdealModule_addSheafHom_toUnit i a
    exact (congrArg (fun t => targetAffineChartIdealModule_addSheafHom i a ≫ t) hmap).trans hsq
  refine ⟨PresheafOfModules.homMk φ ?_⟩
  intro W r m
  have hsW (x : M.val.obj W) :
      q.val.app W (φ.app W x) = α.val.app W x := by
    have h := congrArg (fun t => t.hom.app W) hs
    have h' := ConcreteCategory.congr_hom h x
    exact h'
  apply @schemeModule_mono_app_injective _ _ _ q hq W.unop
  have hα := (α.val.app W).hom.map_smul r m
  have hq' := (q.val.app W).hom.map_smul r (φ.app W m)
  exact (hsW (r • m)).trans
    (hα.trans ((congrArg (r • ·) (hsW m).symm).trans hq'.symm))

/-- The chart comparison is an isomorphism of actual ideal-module
sheaves, since its underlying additive-sheaf map is an isomorphism. -/
theorem targetAffineChartIdealModule_moduleHom_isIso
    {Y Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : Y.affineCover.I₀) :
    IsIso (targetAffineChartIdealModule_moduleHom i a) := by
  let U := Y.affineCover.X a
  let T := SheafOfModules.toSheaf U.ringCatSheaf
  have hT : IsIso (T.map (targetAffineChartIdealModule_moduleHom i a)) := by
    change IsIso (targetAffineChartIdealModule_addSheafHom i a)
    exact targetAffineChartIdealModule_addSheafHom_isIso i a
  exact (isIso_iff_of_reflects_iso _ T).mp hT

/-- The module-sheaf chart isomorphism, with its actual ideal-module
source and target. -/
noncomputable def targetAffineChartIdealModule_moduleIso
    {Y Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : Y.affineCover.I₀) :
    let u := Y.affineCover.f a
    let iU := pullback.fst u i
    IdealSheafDataModule.closedImmersionModule iU ≅
      (Scheme.Modules.restrictFunctor u).obj
        (IdealSheafDataModule.closedImmersionModule i) := by
  letI := targetAffineChartIdealModule_moduleHom_isIso i a
  exact asIso (targetAffineChartIdealModule_moduleHom i a)

/-- The actual ideal-module isomorphism identifies the two inclusion
maps into the structure sheaf on a target chart. -/
theorem targetAffineChartIdealModule_moduleIso_toUnit
    {Y Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : Y.affineCover.I₀) :
    let u := Y.affineCover.f a
    let iU := pullback.fst u i
    (targetAffineChartIdealModule_moduleIso i a).hom ≫
      (Scheme.Modules.restrictFunctor u).map
        (IdealSheafDataModule.closedImmersionModuleToUnit i) ≫
      (Scheme.Modules.restrictUnitIso u).hom =
        IdealSheafDataModule.closedImmersionModuleToUnit iU := by
  let U := Y.affineCover.X a
  let u := Y.affineCover.f a
  let iU := pullback.fst u i
  let T := SheafOfModules.toSheaf U.ringCatSheaf
  let b := (Scheme.Modules.restrictFunctor u).map
    (IdealSheafDataModule.closedImmersionModuleToUnit i)
  let c := (Scheme.Modules.restrictUnitIso u).hom
  apply T.map_injective
  have h1 := T.map_comp ((targetAffineChartIdealModule_moduleIso i a).hom ≫ b) c
  have h2 := T.map_comp (targetAffineChartIdealModule_moduleIso i a).hom b
  have hcomp := h1.trans (congrArg (fun t => t ≫ T.map c) h2)
  have hs := targetAffineChartIdealModule_addSheafHom_toUnit i a
  exact hcomp.trans hs

/-- Flat pullback along a target affine chart preserves monicity of
the restriction of the original ideal-module inclusion. -/
theorem flatTargetAffineChartRestrictIdealPullback_mono
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : Y.affineCover.I₀) :
    let u := Y.affineCover.f a
    let g := Y.affineCover.pullbackHom f a
    Mono ((Scheme.Modules.pullback g).map
      ((Scheme.Modules.restrictFunctor u).map
        (IdealSheafDataModule.closedImmersionModuleToUnit i))) := by
  dsimp only
  let u := Y.affineCover.f a
  let g := Y.affineCover.pullbackHom f a
  let e := targetAffineChartIdealModule_moduleIso i a
  let c := Scheme.Modules.restrictUnitIso u
  let α := IdealSheafDataModule.closedImmersionModuleToUnit
    (pullback.fst u i)
  let b := (Scheme.Modules.restrictFunctor u).map
    (IdealSheafDataModule.closedImmersionModuleToUnit i)
  have hs : e.hom ≫ b ≫ c.hom = α :=
    targetAffineChartIdealModule_moduleIso_toUnit i a
  have hα : Mono ((Scheme.Modules.pullback g).map α) :=
    flatTargetAffineChartClosedImmersionIdealModulePullback_mono f i a
  exact mono_map_middle_of_iso_square (Scheme.Modules.pullback g) e c α b hs hα

/-- On each pulled-back target chart, flatness preserves monicity of
the pullback of the *original* ideal-module inclusion. -/
theorem flatTargetAffineChartOriginalIdealPullback_mono
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : Y.affineCover.I₀) :
    Mono ((Scheme.Modules.pullback
      ((Y.affineCover.pullbackHom f a) ≫ (Y.affineCover.f a))).map
        (IdealSheafDataModule.closedImmersionModuleToUnit i)) := by
  let u := Y.affineCover.f a
  let g := Y.affineCover.pullbackHom f a
  let e₁ : (Scheme.Modules.restrictFunctor u ⋙ Scheme.Modules.pullback g) ≅
      (Scheme.Modules.pullback u ⋙ Scheme.Modules.pullback g) :=
    Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback u)
      (Scheme.Modules.pullback g)
  let e₂ : (Scheme.Modules.pullback u ⋙ Scheme.Modules.pullback g) ≅
      Scheme.Modules.pullback (g ≫ u) :=
    Scheme.Modules.pullbackComp g u
  let e := e₁ ≪≫ e₂
  exact mono_map_of_natIso e
    (IdealSheafDataModule.closedImmersionModuleToUnit i)
    (flatTargetAffineChartRestrictIdealPullback_mono f i a)

/-- Flat pullback preserves the canonical comparison from the actual
ideal module of an arbitrary closed immersion to the kernel of the
base-changed quotient, with no affine hypothesis on either scheme. -/
theorem isIso_flatClosedImmersionIdealPullbackKernelComparison
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (i : Z ⟶ Y) [IsClosedImmersion i] :
    IsIso (closedImmersionIdealPullbackKernelComparison f i) := by
  let 𝒰 := Y.affineCover.pullback₁ f
  apply isIso_closedImmersionIdealPullbackKernelComparison_of_openCover_comp_mono
    f i 𝒰
  intro a
  let u := Y.affineCover.f a
  let g := Y.affineCover.pullbackHom f a
  have heq : (𝒰.f a) ≫ f = g ≫ u := by
    change pullback.fst f u ≫ f = pullback.snd f u ≫ u
    exact pullback.condition
  rw [heq]
  exact flatTargetAffineChartOriginalIdealPullback_mono f i a

end PfaffianDescent
