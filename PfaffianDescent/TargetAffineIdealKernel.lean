import PfaffianDescent.OpenPullbackMono

/-! The ideal-kernel comparison on the pullback of a target affine cover. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- For a flat morphism and a closed immersion over an arbitrary target,
the canonical ideal-kernel comparison is invertible after base change
to each member of the target's affine cover. -/
theorem isIso_flatTargetAffineChartClosedImmersionIdealPullbackKernelComparison
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : Y.affineCover.I₀) :
    IsIso (closedImmersionIdealPullbackKernelComparison
      (Y.affineCover.pullbackHom f a)
      (pullback.fst (Y.affineCover.f a) i)) := by
  have hv : Flat (Y.affineCover.pullbackHom f a) := by
    change Flat (pullback.snd f (Y.affineCover.f a))
    infer_instance
  have hi : IsClosedImmersion (pullback.fst (Y.affineCover.f a) i) := inferInstance
  exact @isIso_flatToSpecClosedImmersionIdealPullbackKernelComparison
    _ _ _ _ (Y.affineCover.pullbackHom f a) hv
    (pullback.fst (Y.affineCover.f a) i) hi

/-- The pulled-back actual ideal inclusion is monic on each affine
chart of an arbitrary target. -/
theorem flatTargetAffineChartClosedImmersionIdealModulePullback_mono
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : Y.affineCover.I₀) :
    Mono ((Scheme.Modules.pullback (Y.affineCover.pullbackHom f a)).map
      (IdealSheafDataModule.closedImmersionModuleToUnit
        (pullback.fst (Y.affineCover.f a) i))) := by
  have hv : Flat (Y.affineCover.pullbackHom f a) := by
    change Flat (pullback.snd f (Y.affineCover.f a))
    infer_instance
  have hi : IsClosedImmersion (pullback.fst (Y.affineCover.f a) i) := inferInstance
  exact @flatToSpecClosedImmersionIdealModulePullback_mono
    _ _ _ _ (Y.affineCover.pullbackHom f a) hv
    (pullback.fst (Y.affineCover.f a) i) hi

/-- The ideal of the base-changed closed immersion on each affine
target chart is exactly the restriction of the original ideal, after
the canonical identification of section rings. -/
theorem targetAffineChartClosedImmersionIdeal_eq_restrict
    {Y Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : Y.affineCover.I₀)
    (V : (Y.affineCover.X a).affineOpens) :
    (pullback.fst (Y.affineCover.f a) i).ker.ideal V =
      (i.ker.ideal
        ⟨(Y.affineCover.f a) ''ᵁ V,
          V.2.image_of_isOpenImmersion (Y.affineCover.f a)⟩).comap
        ((Y.affineCover.f a).appIso V).inv.hom := by
  haveI : QuasiCompact i := inferInstance
  exact Scheme.ker_ideal_of_isPullback_of_isOpenImmersion
    i (pullback.fst (Y.affineCover.f a) i)
    (pullback.snd (Y.affineCover.f a) i)
    (Y.affineCover.f a)
    (IsPullback.of_hasPullback (Y.affineCover.f a) i) V

/-- Every section of the base-changed actual ideal module on an
affine chart comes from a section of the original actual ideal module
on the corresponding affine open of the original target. Their images
in the structure sheaves agree under the chart's section-ring
isomorphism. -/
theorem targetAffineChartIdealModule_section_lift
    {Y Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : Y.affineCover.I₀)
    (V : (Y.affineCover.X a).affineOpens)
    (m : (IdealSheafDataModule.closedImmersionModule
      (pullback.fst (Y.affineCover.f a) i)).val.presheaf.obj
        (Opposite.op V.1)) :
    let u := Y.affineCover.f a
    let iU := pullback.fst u i
    let W : Y.affineOpens :=
      ⟨u ''ᵁ V, V.2.image_of_isOpenImmersion u⟩
    ∃ n : (IdealSheafDataModule.closedImmersionModule i).val.presheaf.obj
        (Opposite.op W.1),
      (u.appIso V).inv.hom
        ((IdealSheafDataModule.closedImmersionModuleToUnit iU).val.app
          (Opposite.op V.1) m) =
        (IdealSheafDataModule.closedImmersionModuleToUnit i).val.app
          (Opposite.op W.1) n := by
  dsimp only
  let u := Y.affineCover.f a
  let iU := pullback.fst u i
  let W : Y.affineOpens := ⟨u ''ᵁ V, V.2.image_of_isOpenImmersion u⟩
  haveI : IsClosedImmersion iU := inferInstance
  have hm : ((IdealSheafDataModule.closedImmersionModuleToUnit iU).val.app
      (Opposite.op V.1) m) ∈ iU.ker.ideal V :=
    IdealSheafDataModule.closedImmersionModule_section_mem_ker_ideal iU V m
  rw [targetAffineChartClosedImmersionIdeal_eq_restrict i a V] at hm
  obtain ⟨n, hn⟩ :=
    IdealSheafDataModule.exists_closedImmersionModule_section_of_affine_mem
      i W _ hm
  exact ⟨n, hn.symm⟩

/-- Conversely, every section of the original ideal module on the image of
an affine target chart restricts to a section of the base-changed ideal
module, compatibly with the section-ring isomorphism. -/
theorem targetAffineChartIdealModule_section_restrict
    {Y Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : Y.affineCover.I₀)
    (V : (Y.affineCover.X a).affineOpens)
    (n : (IdealSheafDataModule.closedImmersionModule i).val.presheaf.obj
      (Opposite.op (⟨(Y.affineCover.f a) ''ᵁ V,
        V.2.image_of_isOpenImmersion (Y.affineCover.f a)⟩ : Y.affineOpens).1)) :
    let u := Y.affineCover.f a
    let iU := pullback.fst u i
    let W : Y.affineOpens :=
      ⟨u ''ᵁ V, V.2.image_of_isOpenImmersion u⟩
    ∃ m : (IdealSheafDataModule.closedImmersionModule iU).val.presheaf.obj
        (Opposite.op V.1),
      (u.appIso V).inv.hom
        ((IdealSheafDataModule.closedImmersionModuleToUnit iU).val.app
          (Opposite.op V.1) m) =
        (IdealSheafDataModule.closedImmersionModuleToUnit i).val.app
          (Opposite.op W.1) n := by
  dsimp only
  let u := Y.affineCover.f a
  let iU := pullback.fst u i
  let W : Y.affineOpens := ⟨u ''ᵁ V, V.2.image_of_isOpenImmersion u⟩
  haveI : IsClosedImmersion iU := inferInstance
  have hn : ((IdealSheafDataModule.closedImmersionModuleToUnit i).val.app
      (Opposite.op W.1) n) ∈ i.ker.ideal W :=
    IdealSheafDataModule.closedImmersionModule_section_mem_ker_ideal i W n
  have hcomp (x : Γ(Y, W.1)) : (u.appIso V).inv.hom ((u.appIso V).hom x) = x := by
    have h := ConcreteCategory.congr_hom (u.appIso V).hom_inv_id x
    simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using h
  have hm : (u.appIso V).hom
      ((IdealSheafDataModule.closedImmersionModuleToUnit i).val.app
        (Opposite.op W.1) n) ∈ iU.ker.ideal V := by
    rw [targetAffineChartClosedImmersionIdeal_eq_restrict i a V]
    change (u.appIso V).inv.hom ((u.appIso V).hom _) ∈ i.ker.ideal W
    exact (hcomp _).symm ▸ hn
  obtain ⟨m, hm'⟩ :=
    IdealSheafDataModule.exists_closedImmersionModule_section_of_affine_mem
      iU V _ hm
  refine ⟨m, ?_⟩
  rw [hm']
  exact hcomp _

/-- The actual ideal-module inclusion is injective on every affine
section set. This makes the preceding section lifts unique. -/
theorem closedImmersionModuleToUnit_affine_injective
    {Y Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (W : Y.affineOpens) :
    Function.Injective
      ((IdealSheafDataModule.closedImmersionModuleToUnit i).val.app
        (Opposite.op W.1)) := by
  have hmono : Mono (IdealSheafDataModule.closedImmersionModuleToUnit i) := by
    change Mono (IdealSheafDataModule.idealModuleToUnit i.ker)
    infer_instance
  let E := SheafOfModules.evaluation Y.ringCatSheaf (Opposite.op W.1)
  have hmonoW : Mono (E.map
      (IdealSheafDataModule.closedImmersionModuleToUnit i)) := inferInstance
  exact (ModuleCat.mono_iff_injective
    (E.map (IdealSheafDataModule.closedImmersionModuleToUnit i))).mp hmonoW

/-- A section of the base-changed ideal module has a unique matching
section of the original ideal module on the corresponding affine open. -/
theorem targetAffineChartIdealModule_section_lift_unique
    {Y Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : Y.affineCover.I₀)
    (V : (Y.affineCover.X a).affineOpens)
    (m : (IdealSheafDataModule.closedImmersionModule
      (pullback.fst (Y.affineCover.f a) i)).val.presheaf.obj
        (Opposite.op V.1)) :
    let u := Y.affineCover.f a
    let iU := pullback.fst u i
    let W : Y.affineOpens :=
      ⟨u ''ᵁ V, V.2.image_of_isOpenImmersion u⟩
    ∃! n : (IdealSheafDataModule.closedImmersionModule i).val.presheaf.obj
        (Opposite.op W.1),
      (u.appIso V).inv.hom
        ((IdealSheafDataModule.closedImmersionModuleToUnit iU).val.app
          (Opposite.op V.1) m) =
        (IdealSheafDataModule.closedImmersionModuleToUnit i).val.app
          (Opposite.op W.1) n := by
  dsimp only
  obtain ⟨n, hn⟩ := targetAffineChartIdealModule_section_lift i a V m
  refine ⟨n, hn, ?_⟩
  intro n' hn'
  apply closedImmersionModuleToUnit_affine_injective i
    ⟨(Y.affineCover.f a) ''ᵁ V,
      V.2.image_of_isOpenImmersion (Y.affineCover.f a)⟩
  exact hn'.symm.trans hn

/-- A section of the original ideal module on an affine chart image has
a unique matching section of the base-changed ideal module. -/
theorem targetAffineChartIdealModule_section_restrict_unique
    {Y Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : Y.affineCover.I₀)
    (V : (Y.affineCover.X a).affineOpens)
    (n : (IdealSheafDataModule.closedImmersionModule i).val.presheaf.obj
      (Opposite.op (⟨(Y.affineCover.f a) ''ᵁ V,
        V.2.image_of_isOpenImmersion (Y.affineCover.f a)⟩ : Y.affineOpens).1)) :
    let u := Y.affineCover.f a
    let iU := pullback.fst u i
    let W : Y.affineOpens :=
      ⟨u ''ᵁ V, V.2.image_of_isOpenImmersion u⟩
    ∃! m : (IdealSheafDataModule.closedImmersionModule iU).val.presheaf.obj
        (Opposite.op V.1),
      (u.appIso V).inv.hom
        ((IdealSheafDataModule.closedImmersionModuleToUnit iU).val.app
          (Opposite.op V.1) m) =
        (IdealSheafDataModule.closedImmersionModuleToUnit i).val.app
          (Opposite.op W.1) n := by
  dsimp only
  obtain ⟨m, hm⟩ := targetAffineChartIdealModule_section_restrict i a V n
  refine ⟨m, hm, ?_⟩
  intro m' hm'
  apply closedImmersionModuleToUnit_affine_injective
    (pullback.fst (Y.affineCover.f a) i) V
  have h := hm'.trans hm.symm
  exact ((Y.affineCover.f a).appIso V).commRingCatIsoToRingEquiv.symm.injective h

/-- The two actual ideal modules have canonically equivalent section
sets on each affine target chart, characterized by their inclusions
into the structure sheaf. -/
noncomputable def targetAffineChartIdealModule_sectionsEquiv
    {Y Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : Y.affineCover.I₀)
    (V : (Y.affineCover.X a).affineOpens) :
    (IdealSheafDataModule.closedImmersionModule
      (pullback.fst (Y.affineCover.f a) i)).val.presheaf.obj
        (Opposite.op V.1) ≃
      (IdealSheafDataModule.closedImmersionModule i).val.presheaf.obj
        (Opposite.op
          (⟨(Y.affineCover.f a) ''ᵁ V,
            V.2.image_of_isOpenImmersion (Y.affineCover.f a)⟩ : Y.affineOpens).1) := by
  classical
  let u := Y.affineCover.f a
  let iU := pullback.fst u i
  let W : Y.affineOpens := ⟨u ''ᵁ V, V.2.image_of_isOpenImmersion u⟩
  let F : (IdealSheafDataModule.closedImmersionModule iU).val.presheaf.obj
      (Opposite.op V.1) →
      (IdealSheafDataModule.closedImmersionModule i).val.presheaf.obj
        (Opposite.op W.1) :=
    fun m => (targetAffineChartIdealModule_section_lift_unique i a V m).choose
  have hF (m) : (u.appIso V).inv.hom
      ((IdealSheafDataModule.closedImmersionModuleToUnit iU).val.app
        (Opposite.op V.1) m) =
      (IdealSheafDataModule.closedImmersionModuleToUnit i).val.app
        (Opposite.op W.1) (F m) :=
    (targetAffineChartIdealModule_section_lift_unique i a V m).choose_spec.1
  refine Equiv.ofBijective F ?_
  constructor
  · intro m₁ m₂ h
    apply closedImmersionModuleToUnit_affine_injective iU V
    have h₁ := hF m₁
    have h₂ := hF m₂
    rw [h] at h₁
    exact (u.appIso V).commRingCatIsoToRingEquiv.symm.injective (h₁.trans h₂.symm)
  · intro n
    obtain ⟨m, hm⟩ := targetAffineChartIdealModule_section_restrict i a V n
    refine ⟨m, ?_⟩
    apply closedImmersionModuleToUnit_affine_injective i W
    exact (hF m).symm.trans hm

/-- The affine section equivalence agrees with the inclusion of the
actual ideal modules into their structure sheaves. -/
@[simp]
theorem targetAffineChartIdealModule_sectionsEquiv_toUnit
    {Y Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : Y.affineCover.I₀)
    (V : (Y.affineCover.X a).affineOpens)
    (m : (IdealSheafDataModule.closedImmersionModule
      (pullback.fst (Y.affineCover.f a) i)).val.presheaf.obj
        (Opposite.op V.1)) :
    let u := Y.affineCover.f a
    let iU := pullback.fst u i
    let W : Y.affineOpens := ⟨u ''ᵁ V, V.2.image_of_isOpenImmersion u⟩
    (u.appIso V).inv.hom
      ((IdealSheafDataModule.closedImmersionModuleToUnit iU).val.app
        (Opposite.op V.1) m) =
      (IdealSheafDataModule.closedImmersionModuleToUnit i).val.app
        (Opposite.op W.1)
        (targetAffineChartIdealModule_sectionsEquiv i a V m) := by
  dsimp only [targetAffineChartIdealModule_sectionsEquiv]
  exact (targetAffineChartIdealModule_section_lift_unique i a V m).choose_spec.1

/-- The affine section equivalence preserves addition. -/
theorem targetAffineChartIdealModule_sectionsEquiv_map_add
    {Y Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : Y.affineCover.I₀)
    (V : (Y.affineCover.X a).affineOpens)
    (m n : (IdealSheafDataModule.closedImmersionModule
      (pullback.fst (Y.affineCover.f a) i)).val.presheaf.obj
        (Opposite.op V.1)) :
    targetAffineChartIdealModule_sectionsEquiv i a V (m + n) =
      targetAffineChartIdealModule_sectionsEquiv i a V m +
      targetAffineChartIdealModule_sectionsEquiv i a V n := by
  let u := Y.affineCover.f a
  let iU := pullback.fst u i
  let W : Y.affineOpens := ⟨u ''ᵁ V, V.2.image_of_isOpenImmersion u⟩
  let e := targetAffineChartIdealModule_sectionsEquiv i a V
  let α := (IdealSheafDataModule.closedImmersionModuleToUnit iU).val.app
    (Opposite.op V.1)
  let β := (IdealSheafDataModule.closedImmersionModuleToUnit i).val.app
    (Opposite.op W.1)
  have h (x) : (u.appIso V).inv.hom (α x) = β (e x) :=
    targetAffineChartIdealModule_sectionsEquiv_toUnit i a V x
  apply closedImmersionModuleToUnit_affine_injective i W
  change β (e (m + n)) = β (e m + e n)
  have hα : (u.appIso V).inv.hom (α (m + n)) =
      (u.appIso V).inv.hom (α m) + (u.appIso V).inv.hom (α n) := by
    change (u.appIso V).inv.hom (α.hom (m + n)) =
      (u.appIso V).inv.hom (α.hom m) + (u.appIso V).inv.hom (α.hom n)
    exact (congrArg (u.appIso V).inv.hom (α.hom.map_add m n)).trans
      ((u.appIso V).inv.hom.map_add (α.hom m) (α.hom n))
  have hβ : β (e m) + β (e n) = β (e m + e n) := by
    change β.hom (e m) + β.hom (e n) = β.hom (e m + e n)
    exact (β.hom.map_add (e m) (e n)).symm
  exact (h (m + n)).symm.trans
    (hα.trans ((congrArg₂ (· + ·) (h m) (h n)).trans hβ))

/-- Additive form of the affine chart comparison for the actual
closed-immersion ideal modules. -/
noncomputable def targetAffineChartIdealModule_sectionsAddEquiv
    {Y Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : Y.affineCover.I₀)
    (V : (Y.affineCover.X a).affineOpens) :
    (IdealSheafDataModule.closedImmersionModule
      (pullback.fst (Y.affineCover.f a) i)).val.presheaf.obj
        (Opposite.op V.1) ≃+
      (IdealSheafDataModule.closedImmersionModule i).val.presheaf.obj
        (Opposite.op
          (⟨(Y.affineCover.f a) ''ᵁ V,
            V.2.image_of_isOpenImmersion (Y.affineCover.f a)⟩ : Y.affineOpens).1) :=
  { toEquiv := targetAffineChartIdealModule_sectionsEquiv i a V
    map_add' := targetAffineChartIdealModule_sectionsEquiv_map_add i a V }

/-- On nested affine opens, the chart comparison commutes with
restriction of actual ideal-module sections. -/
theorem targetAffineChartIdealModule_sectionsEquiv_natural
    {Y Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : Y.affineCover.I₀)
    (V W : (Y.affineCover.X a).affineOpens)
    (j : Opposite.op W.1 ⟶ Opposite.op V.1)
    (m : (IdealSheafDataModule.closedImmersionModule
      (pullback.fst (Y.affineCover.f a) i)).val.presheaf.obj
        (Opposite.op W.1)) :
    targetAffineChartIdealModule_sectionsEquiv i a V
      ((IdealSheafDataModule.closedImmersionModule
        (pullback.fst (Y.affineCover.f a) i)).val.presheaf.map j m) =
      (IdealSheafDataModule.closedImmersionModule i).val.presheaf.map
        ((Y.affineCover.f a).opensFunctor.op.map j)
        (targetAffineChartIdealModule_sectionsEquiv i a W m) := by
  let u := Y.affineCover.f a
  let iU := pullback.fst u i
  let MV := IdealSheafDataModule.closedImmersionModule iU
  let MY := IdealSheafDataModule.closedImmersionModule i
  let α := IdealSheafDataModule.closedImmersionModuleToUnit iU
  let β := IdealSheafDataModule.closedImmersionModuleToUnit i
  have hmono := closedImmersionModuleToUnit_affine_injective i
    ⟨u ''ᵁ V, V.2.image_of_isOpenImmersion u⟩
  apply hmono
  have hα := α.val.naturality j
  have hβ := β.val.naturality (u.opensFunctor.op.map j)
  have hι := u.appIso_inv_naturality j
  have hα' : α.val.app (Opposite.op V.1) (MV.val.presheaf.map j m) =
      (Y.affineCover.X a).presheaf.map j
        (α.val.app (Opposite.op W.1) m) := by
    have h := ConcreteCategory.congr_hom hα m
    exact h
  have hβ' (n : MY.val.presheaf.obj (Opposite.op (u ''ᵁ W.1))) :
      β.val.app (Opposite.op (u ''ᵁ V.1))
        (MY.val.presheaf.map (u.opensFunctor.op.map j) n) =
      Y.presheaf.map (u.opensFunctor.op.map j)
        (β.val.app (Opposite.op (u ''ᵁ W.1)) n) := by
    have h := ConcreteCategory.congr_hom hβ n
    exact h
  have hι' (x : Γ(Y.affineCover.X a, W.1)) :
      (u.appIso V).inv.hom ((Y.affineCover.X a).presheaf.map j x) =
      Y.presheaf.map (u.opensFunctor.op.map j) ((u.appIso W).inv.hom x) := by
    have h := ConcreteCategory.congr_hom hι x
    exact h
  have hV := targetAffineChartIdealModule_sectionsEquiv_toUnit i a V
    (MV.val.presheaf.map j m)
  have hW := targetAffineChartIdealModule_sectionsEquiv_toUnit i a W m
  have h1 := congrArg (u.appIso V).inv.hom hα'
  have h2 := hι' (α.val.app (Opposite.op W.1) m)
  have h3 := congrArg (Y.presheaf.map (u.opensFunctor.op.map j)) hW
  have h4 := (hβ' (targetAffineChartIdealModule_sectionsEquiv i a W m)).symm
  exact hV.symm.trans (h1.trans (h2.trans (h3.trans h4)))

/-- The affine comparison transports scalar multiplication through
the canonical isomorphism of section rings. -/
theorem targetAffineChartIdealModule_sectionsEquiv_smul
    {Y Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : Y.affineCover.I₀)
    (V : (Y.affineCover.X a).affineOpens)
    (r : Γ(Y.affineCover.X a, V.1))
    (m : (IdealSheafDataModule.closedImmersionModule
      (pullback.fst (Y.affineCover.f a) i)).val.presheaf.obj
        (Opposite.op V.1)) :
    letI : Module (Γ(Y.affineCover.X a, V.1))
        ((IdealSheafDataModule.closedImmersionModule
          (pullback.fst (Y.affineCover.f a) i)).val.presheaf.obj
            (Opposite.op V.1)) := by
      change Module (((Y.affineCover.X a).ringCatSheaf.obj).obj
        (Opposite.op V.1)) _
      infer_instance
    letI : Module (Γ(Y, (Y.affineCover.f a) ''ᵁ V.1))
        ((IdealSheafDataModule.closedImmersionModule i).val.presheaf.obj
          (Opposite.op ((Y.affineCover.f a) ''ᵁ V.1))) := by
      change Module ((Y.ringCatSheaf.obj).obj
        (Opposite.op ((Y.affineCover.f a) ''ᵁ V.1))) _
      infer_instance
    targetAffineChartIdealModule_sectionsEquiv i a V (r • m) =
      ((Y.affineCover.f a).appIso V).inv.hom r •
        targetAffineChartIdealModule_sectionsEquiv i a V m := by
  letI : Module (Γ(Y.affineCover.X a, V.1))
      ((IdealSheafDataModule.closedImmersionModule
        (pullback.fst (Y.affineCover.f a) i)).val.presheaf.obj
          (Opposite.op V.1)) := by
    change Module (((Y.affineCover.X a).ringCatSheaf.obj).obj
      (Opposite.op V.1)) _
    infer_instance
  letI : Module (Γ(Y, (Y.affineCover.f a) ''ᵁ V.1))
      ((IdealSheafDataModule.closedImmersionModule i).val.presheaf.obj
        (Opposite.op ((Y.affineCover.f a) ''ᵁ V.1))) := by
    change Module ((Y.ringCatSheaf.obj).obj
      (Opposite.op ((Y.affineCover.f a) ''ᵁ V.1))) _
    infer_instance
  let u := Y.affineCover.f a
  let iU := pullback.fst u i
  let W : Y.affineOpens := ⟨u ''ᵁ V, V.2.image_of_isOpenImmersion u⟩
  let e := targetAffineChartIdealModule_sectionsEquiv i a V
  let α := (IdealSheafDataModule.closedImmersionModuleToUnit iU).val.app
    (Opposite.op V.1)
  let β := (IdealSheafDataModule.closedImmersionModuleToUnit i).val.app
    (Opposite.op W.1)
  have h (x) : (u.appIso V).inv.hom (α x) = β (e x) :=
    targetAffineChartIdealModule_sectionsEquiv_toUnit i a V x
  apply closedImmersionModuleToUnit_affine_injective i W
  change β (e (r • m)) = β ((u.appIso V).inv.hom r • e m)
  have hα : (u.appIso V).inv.hom (α (r • m)) =
      (u.appIso V).inv.hom r • (u.appIso V).inv.hom (α m) := by
    have hα₀ := α.hom.map_smul r m
    have hα₁ := congrArg (u.appIso V).inv.hom hα₀
    let x : Γ(Y.affineCover.X a, V.1) := α.hom m
    have hα₂ := (u.appIso V).inv.hom.map_mul r x
    exact hα₁.trans hα₂
  let s : Γ(Y, W.1) := (u.appIso V).inv.hom r
  have hβ := (β.hom.map_smul s (e m)).symm
  exact (h (r • m)).symm.trans
    (hα.trans ((congrArg (s • ·) (h m)).trans hβ))


end PfaffianDescent
