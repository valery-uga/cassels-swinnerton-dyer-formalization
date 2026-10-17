import PfaffianDescent.TargetAffineIdealSheaf

/-! Ideal-module comparison for arbitrary open immersions. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

/-- The ideal of a closed immersion restricted along any open immersion
has the expected affine sections. -/
theorem openImmersionClosedImmersionIdeal_eq_restrict
    {Y Z U : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (u : U ⟶ Y) [IsOpenImmersion u] (V : U.affineOpens) :
    (pullback.fst u i).ker.ideal V =
      (i.ker.ideal
        ⟨u ''ᵁ V, V.2.image_of_isOpenImmersion u⟩).comap
        (u.appIso V).inv.hom := by
  haveI : QuasiCompact i := inferInstance
  exact Scheme.ker_ideal_of_isPullback_of_isOpenImmersion
    i (pullback.fst u i) (pullback.snd u i) u
    (IsPullback.of_hasPullback u i) V

/-- An ideal-module section on an affine open of the restricted scheme
lifts to the original ideal module on its image affine open. -/
theorem openImmersionIdealModule_section_lift
    {Y Z U : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (u : U ⟶ Y) [IsOpenImmersion u] (V : U.affineOpens)
    (m : (IdealSheafDataModule.closedImmersionModule
      (pullback.fst u i)).val.presheaf.obj (Opposite.op V.1)) :
    let iU := pullback.fst u i
    let W : Y.affineOpens := ⟨u ''ᵁ V, V.2.image_of_isOpenImmersion u⟩
    ∃ n : (IdealSheafDataModule.closedImmersionModule i).val.presheaf.obj
        (Opposite.op W.1),
      (u.appIso V).inv.hom
        ((IdealSheafDataModule.closedImmersionModuleToUnit iU).val.app
          (Opposite.op V.1) m) =
        (IdealSheafDataModule.closedImmersionModuleToUnit i).val.app
          (Opposite.op W.1) n := by
  dsimp only
  let iU := pullback.fst u i
  let W : Y.affineOpens := ⟨u ''ᵁ V, V.2.image_of_isOpenImmersion u⟩
  haveI : IsClosedImmersion iU := inferInstance
  have hm : ((IdealSheafDataModule.closedImmersionModuleToUnit iU).val.app
      (Opposite.op V.1) m) ∈ iU.ker.ideal V :=
    IdealSheafDataModule.closedImmersionModule_section_mem_ker_ideal iU V m
  rw [openImmersionClosedImmersionIdeal_eq_restrict i u V] at hm
  obtain ⟨n, hn⟩ :=
    IdealSheafDataModule.exists_closedImmersionModule_section_of_affine_mem
      i W _ hm
  exact ⟨n, hn.symm⟩

/-- Conversely, a section of the original ideal module on the image of
an affine open restricts to the ideal module of the base-changed immersion. -/
theorem openImmersionIdealModule_section_restrict
    {Y Z U : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (u : U ⟶ Y) [IsOpenImmersion u] (V : U.affineOpens)
    (n : (IdealSheafDataModule.closedImmersionModule i).val.presheaf.obj
      (Opposite.op (⟨u ''ᵁ V,
        V.2.image_of_isOpenImmersion u⟩ : Y.affineOpens).1)) :
    let iU := pullback.fst u i
    let W : Y.affineOpens := ⟨u ''ᵁ V, V.2.image_of_isOpenImmersion u⟩
    ∃ m : (IdealSheafDataModule.closedImmersionModule iU).val.presheaf.obj
        (Opposite.op V.1),
      (u.appIso V).inv.hom
        ((IdealSheafDataModule.closedImmersionModuleToUnit iU).val.app
          (Opposite.op V.1) m) =
        (IdealSheafDataModule.closedImmersionModuleToUnit i).val.app
          (Opposite.op W.1) n := by
  dsimp only
  let iU := pullback.fst u i
  let W : Y.affineOpens := ⟨u ''ᵁ V, V.2.image_of_isOpenImmersion u⟩
  haveI : IsClosedImmersion iU := inferInstance
  have hn : ((IdealSheafDataModule.closedImmersionModuleToUnit i).val.app
      (Opposite.op W.1) n) ∈ i.ker.ideal W :=
    IdealSheafDataModule.closedImmersionModule_section_mem_ker_ideal i W n
  have hcomp (x : Γ(Y, W.1)) :
      (u.appIso V).inv.hom ((u.appIso V).hom x) = x := by
    have h := ConcreteCategory.congr_hom (u.appIso V).hom_inv_id x
    simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using h
  have hm : (u.appIso V).hom
      ((IdealSheafDataModule.closedImmersionModuleToUnit i).val.app
        (Opposite.op W.1) n) ∈ iU.ker.ideal V := by
    rw [openImmersionClosedImmersionIdeal_eq_restrict i u V]
    change (u.appIso V).inv.hom ((u.appIso V).hom _) ∈ i.ker.ideal W
    exact (hcomp _).symm ▸ hn
  obtain ⟨m, hm'⟩ :=
    IdealSheafDataModule.exists_closedImmersionModule_section_of_affine_mem
      iU V _ hm
  refine ⟨m, ?_⟩
  rw [hm']
  exact hcomp _

/-- A section of the base-changed ideal module has a unique matching
section of the original ideal module on the corresponding affine open. -/
theorem openImmersionIdealModule_section_lift_unique
    {Y Z U : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (u : U ⟶ Y) [IsOpenImmersion u]
    (V : U.affineOpens)
    (m : (IdealSheafDataModule.closedImmersionModule
      (pullback.fst u i)).val.presheaf.obj
        (Opposite.op V.1)) :
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
  obtain ⟨n, hn⟩ := openImmersionIdealModule_section_lift i u V m
  refine ⟨n, hn, ?_⟩
  intro n' hn'
  apply closedImmersionModuleToUnit_affine_injective i
    ⟨u ''ᵁ V,
      V.2.image_of_isOpenImmersion u⟩
  exact hn'.symm.trans hn

/-- A section of the original ideal module on an affine chart image has
a unique matching section of the base-changed ideal module. -/
theorem openImmersionIdealModule_section_restrict_unique
    {Y Z U : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (u : U ⟶ Y) [IsOpenImmersion u]
    (V : U.affineOpens)
    (n : (IdealSheafDataModule.closedImmersionModule i).val.presheaf.obj
      (Opposite.op (⟨u ''ᵁ V,
        V.2.image_of_isOpenImmersion u⟩ : Y.affineOpens).1)) :
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
  obtain ⟨m, hm⟩ := openImmersionIdealModule_section_restrict i u V n
  refine ⟨m, hm, ?_⟩
  intro m' hm'
  apply closedImmersionModuleToUnit_affine_injective
    (pullback.fst u i) V
  have h := hm'.trans hm.symm
  exact (u.appIso V).commRingCatIsoToRingEquiv.symm.injective h

/-- The two actual ideal modules have canonically equivalent section
sets on each affine target chart, characterized by their inclusions
into the structure sheaf. -/
noncomputable def openImmersionIdealModule_sectionsEquiv
    {Y Z U : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (u : U ⟶ Y) [IsOpenImmersion u]
    (V : U.affineOpens) :
    (IdealSheafDataModule.closedImmersionModule
      (pullback.fst u i)).val.presheaf.obj
        (Opposite.op V.1) ≃
      (IdealSheafDataModule.closedImmersionModule i).val.presheaf.obj
        (Opposite.op
          (⟨u ''ᵁ V,
            V.2.image_of_isOpenImmersion u⟩ : Y.affineOpens).1) := by
  classical
  let iU := pullback.fst u i
  let W : Y.affineOpens := ⟨u ''ᵁ V, V.2.image_of_isOpenImmersion u⟩
  let F : (IdealSheafDataModule.closedImmersionModule iU).val.presheaf.obj
      (Opposite.op V.1) →
      (IdealSheafDataModule.closedImmersionModule i).val.presheaf.obj
        (Opposite.op W.1) :=
    fun m => (openImmersionIdealModule_section_lift_unique i u V m).choose
  have hF (m) : (u.appIso V).inv.hom
      ((IdealSheafDataModule.closedImmersionModuleToUnit iU).val.app
        (Opposite.op V.1) m) =
      (IdealSheafDataModule.closedImmersionModuleToUnit i).val.app
        (Opposite.op W.1) (F m) :=
    (openImmersionIdealModule_section_lift_unique i u V m).choose_spec.1
  refine Equiv.ofBijective F ?_
  constructor
  · intro m₁ m₂ h
    apply closedImmersionModuleToUnit_affine_injective iU V
    have h₁ := hF m₁
    have h₂ := hF m₂
    rw [h] at h₁
    exact (u.appIso V).commRingCatIsoToRingEquiv.symm.injective (h₁.trans h₂.symm)
  · intro n
    obtain ⟨m, hm⟩ := openImmersionIdealModule_section_restrict i u V n
    refine ⟨m, ?_⟩
    apply closedImmersionModuleToUnit_affine_injective i W
    exact (hF m).symm.trans hm

/-- The affine section equivalence agrees with the inclusion of the
actual ideal modules into their structure sheaves. -/
@[simp]
theorem openImmersionIdealModule_sectionsEquiv_toUnit
    {Y Z U : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (u : U ⟶ Y) [IsOpenImmersion u]
    (V : U.affineOpens)
    (m : (IdealSheafDataModule.closedImmersionModule
      (pullback.fst u i)).val.presheaf.obj
        (Opposite.op V.1)) :
  let iU := pullback.fst u i
    let W : Y.affineOpens := ⟨u ''ᵁ V, V.2.image_of_isOpenImmersion u⟩
    (u.appIso V).inv.hom
      ((IdealSheafDataModule.closedImmersionModuleToUnit iU).val.app
        (Opposite.op V.1) m) =
      (IdealSheafDataModule.closedImmersionModuleToUnit i).val.app
        (Opposite.op W.1)
        (openImmersionIdealModule_sectionsEquiv i u V m) := by
  dsimp only [openImmersionIdealModule_sectionsEquiv]
  exact (openImmersionIdealModule_section_lift_unique i u V m).choose_spec.1


/-- The affine section equivalence preserves addition. -/
theorem openImmersionIdealModule_sectionsEquiv_map_add
    {Y Z U : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (u : U ⟶ Y) [IsOpenImmersion u]
    (V : U.affineOpens)
    (m n : (IdealSheafDataModule.closedImmersionModule
      (pullback.fst u i)).val.presheaf.obj
        (Opposite.op V.1)) :
    openImmersionIdealModule_sectionsEquiv i u V (m + n) =
      openImmersionIdealModule_sectionsEquiv i u V m +
      openImmersionIdealModule_sectionsEquiv i u V n := by
  let iU := pullback.fst u i
  let W : Y.affineOpens := ⟨u ''ᵁ V, V.2.image_of_isOpenImmersion u⟩
  let e := openImmersionIdealModule_sectionsEquiv i u V
  let α := (IdealSheafDataModule.closedImmersionModuleToUnit iU).val.app
    (Opposite.op V.1)
  let β := (IdealSheafDataModule.closedImmersionModuleToUnit i).val.app
    (Opposite.op W.1)
  have h (x) : (u.appIso V).inv.hom (α x) = β (e x) :=
    openImmersionIdealModule_sectionsEquiv_toUnit i u V x
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
noncomputable def openImmersionIdealModule_sectionsAddEquiv
    {Y Z U : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (u : U ⟶ Y) [IsOpenImmersion u]
    (V : U.affineOpens) :
    (IdealSheafDataModule.closedImmersionModule
      (pullback.fst u i)).val.presheaf.obj
        (Opposite.op V.1) ≃+
      (IdealSheafDataModule.closedImmersionModule i).val.presheaf.obj
        (Opposite.op
          (⟨u ''ᵁ V,
            V.2.image_of_isOpenImmersion u⟩ : Y.affineOpens).1) :=
  { toEquiv := openImmersionIdealModule_sectionsEquiv i u V
    map_add' := openImmersionIdealModule_sectionsEquiv_map_add i u V }

/-- On nested affine opens, the chart comparison commutes with
restriction of actual ideal-module sections. -/
theorem openImmersionIdealModule_sectionsEquiv_natural
    {Y Z U : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (u : U ⟶ Y) [IsOpenImmersion u]
    (V W : U.affineOpens)
    (j : Opposite.op W.1 ⟶ Opposite.op V.1)
    (m : (IdealSheafDataModule.closedImmersionModule
      (pullback.fst u i)).val.presheaf.obj
        (Opposite.op W.1)) :
    openImmersionIdealModule_sectionsEquiv i u V
      ((IdealSheafDataModule.closedImmersionModule
        (pullback.fst u i)).val.presheaf.map j m) =
      (IdealSheafDataModule.closedImmersionModule i).val.presheaf.map
        (u.opensFunctor.op.map j)
        (openImmersionIdealModule_sectionsEquiv i u W m) := by
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
      U.presheaf.map j
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
  have hι' (x : Γ(U, W.1)) :
      (u.appIso V).inv.hom (U.presheaf.map j x) =
      Y.presheaf.map (u.opensFunctor.op.map j) ((u.appIso W).inv.hom x) := by
    have h := ConcreteCategory.congr_hom hι x
    exact h
  have hV := openImmersionIdealModule_sectionsEquiv_toUnit i u V
    (MV.val.presheaf.map j m)
  have hW := openImmersionIdealModule_sectionsEquiv_toUnit i u W m
  have h1 := congrArg (u.appIso V).inv.hom hα'
  have h2 := hι' (α.val.app (Opposite.op W.1) m)
  have h3 := congrArg (Y.presheaf.map (u.opensFunctor.op.map j)) hW
  have h4 := (hβ' (openImmersionIdealModule_sectionsEquiv i u W m)).symm
  exact hV.symm.trans (h1.trans (h2.trans (h3.trans h4)))

/-- The affine comparison transports scalar multiplication through
the canonical isomorphism of section rings. -/
theorem openImmersionIdealModule_sectionsEquiv_smul
    {Y Z U : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (u : U ⟶ Y) [IsOpenImmersion u]
    (V : U.affineOpens)
    (r : Γ(U, V.1))
    (m : (IdealSheafDataModule.closedImmersionModule
      (pullback.fst u i)).val.presheaf.obj
        (Opposite.op V.1)) :
    letI : Module (Γ(U, V.1))
        ((IdealSheafDataModule.closedImmersionModule
          (pullback.fst u i)).val.presheaf.obj
            (Opposite.op V.1)) := by
      change Module ((U.ringCatSheaf.obj).obj
        (Opposite.op V.1)) _
      infer_instance
    letI : Module (Γ(Y, u ''ᵁ V.1))
        ((IdealSheafDataModule.closedImmersionModule i).val.presheaf.obj
          (Opposite.op (u ''ᵁ V.1))) := by
      change Module ((Y.ringCatSheaf.obj).obj
        (Opposite.op (u ''ᵁ V.1))) _
      infer_instance
    openImmersionIdealModule_sectionsEquiv i u V (r • m) =
      (u.appIso V).inv.hom r •
        openImmersionIdealModule_sectionsEquiv i u V m := by
  letI : Module (Γ(U, V.1))
      ((IdealSheafDataModule.closedImmersionModule
        (pullback.fst u i)).val.presheaf.obj
          (Opposite.op V.1)) := by
    change Module ((U.ringCatSheaf.obj).obj
      (Opposite.op V.1)) _
    infer_instance
  letI : Module (Γ(Y, u ''ᵁ V.1))
      ((IdealSheafDataModule.closedImmersionModule i).val.presheaf.obj
        (Opposite.op (u ''ᵁ V.1))) := by
    change Module ((Y.ringCatSheaf.obj).obj
      (Opposite.op (u ''ᵁ V.1))) _
    infer_instance
  let iU := pullback.fst u i
  let W : Y.affineOpens := ⟨u ''ᵁ V, V.2.image_of_isOpenImmersion u⟩
  let e := openImmersionIdealModule_sectionsEquiv i u V
  let α := (IdealSheafDataModule.closedImmersionModuleToUnit iU).val.app
    (Opposite.op V.1)
  let β := (IdealSheafDataModule.closedImmersionModuleToUnit i).val.app
    (Opposite.op W.1)
  have h (x) : (u.appIso V).inv.hom (α x) = β (e x) :=
    openImmersionIdealModule_sectionsEquiv_toUnit i u V x
  apply closedImmersionModuleToUnit_affine_injective i W
  change β (e (r • m)) = β ((u.appIso V).inv.hom r • e m)
  have hα : (u.appIso V).inv.hom (α (r • m)) =
      (u.appIso V).inv.hom r • (u.appIso V).inv.hom (α m) := by
    have hα₀ := α.hom.map_smul r m
    have hα₁ := congrArg (u.appIso V).inv.hom hα₀
    let x : Γ(U, V.1) := α.hom m
    have hα₂ := (u.appIso V).inv.hom.map_mul r x
    exact hα₁.trans hα₂
  let s : Γ(Y, W.1) := (u.appIso V).inv.hom r
  have hβ := (β.hom.map_smul s (e m)).symm
  exact (h (r • m)).symm.trans
    (hα.trans ((congrArg (s • ·) (h m)).trans hβ))


/-- The checked comparison of actual ideal-module sections defines a
natural transformation on the affine-open basis of a target chart. -/
noncomputable def openImmersionIdealModule_basisNatTrans
    {Y Z U : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (u : U ⟶ Y) [IsOpenImmersion u] :
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
      (openImmersionIdealModule_sectionsAddEquiv i u V.unop).toAddMonoidHom
  · intro V W j
    ext m
    exact openImmersionIdealModule_sectionsEquiv_natural i u W.unop V.unop
      ((inducedFunctor (fun V : U.affineOpens => V.1)).op.map j) m

/-- The affine-basis comparison extends uniquely to an additive sheaf
morphism on the entire target chart. -/
noncomputable def openImmersionIdealModule_addSheafHom
    {Y Z U : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (u : U ⟶ Y) [IsOpenImmersion u] :
    let iU := pullback.fst u i
    (SheafOfModules.toSheaf U.ringCatSheaf).obj
      (IdealSheafDataModule.closedImmersionModule iU) ⟶
    (SheafOfModules.toSheaf U.ringCatSheaf).obj
      ((Scheme.Modules.restrictFunctor u).obj
        (IdealSheafDataModule.closedImmersionModule i)) := by
  dsimp only
  let B : U.affineOpens → Opens U := fun V => V.1
  have hB : Opens.IsBasis (Set.range B) := by
    simpa [B] using U.isBasis_affineOpens
  exact ⟨TopCat.Sheaf.restrictHomEquivHom _ _ hB
    (openImmersionIdealModule_basisNatTrans i u)⟩

/-- The additive sheaf comparison is an isomorphism because it is an
isomorphism on every member of the affine-open basis. -/
theorem openImmersionIdealModule_addSheafHom_isIso
    {Y Z U : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (u : U ⟶ Y) [IsOpenImmersion u] :
    IsIso (openImmersionIdealModule_addSheafHom i u) := by
  let B : U.affineOpens → Opens U := fun V => V.1
  have hB : Opens.IsBasis (Set.range B) := by
    simpa [B] using U.isBasis_affineOpens
  apply TopCat.Sheaf.isIso_iff_isIso_basis hB
  intro V
  change IsIso ((TopCat.Sheaf.restrictHomEquivHom _ _ hB
    (openImmersionIdealModule_basisNatTrans i u)).app
      (Opposite.op (B V)))
  have heq := TopCat.Sheaf.extend_hom_app _ _ hB
    (openImmersionIdealModule_basisNatTrans i u) V
  have hi : IsIso ((openImmersionIdealModule_basisNatTrans i u).app
      (Opposite.op V)) := by
    change IsIso
      ((openImmersionIdealModule_sectionsAddEquiv i u V).toAddCommGrpIso.hom)
    infer_instance
  exact heq.symm ▸ hi

/-- The actual ideal modules on a target chart are isomorphic as
underlying additive sheaves. -/
noncomputable def openImmersionIdealModule_addSheafIso
    {Y Z U : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (u : U ⟶ Y) [IsOpenImmersion u] :
    let iU := pullback.fst u i
    (SheafOfModules.toSheaf U.ringCatSheaf).obj
      (IdealSheafDataModule.closedImmersionModule iU) ≅
    (SheafOfModules.toSheaf U.ringCatSheaf).obj
      ((Scheme.Modules.restrictFunctor u).obj
        (IdealSheafDataModule.closedImmersionModule i)) := by
  letI := openImmersionIdealModule_addSheafHom_isIso i u
  exact asIso (openImmersionIdealModule_addSheafHom i u)

/-- On affine opens, the global additive sheaf comparison is the
explicit checked section equivalence. -/
theorem openImmersionIdealModule_addSheafHom_app_affine
    {Y Z U : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (u : U ⟶ Y) [IsOpenImmersion u]
    (V : U.affineOpens) :
    (openImmersionIdealModule_addSheafHom i u).hom.app
      (Opposite.op V.1) =
      AddCommGrpCat.ofHom
        (openImmersionIdealModule_sectionsAddEquiv i u V).toAddMonoidHom := by
  let B : U.affineOpens → Opens U := fun V => V.1
  have hB : Opens.IsBasis (Set.range B) := by
    simpa [B] using U.isBasis_affineOpens
  exact TopCat.Sheaf.extend_hom_app _ _ hB
    (openImmersionIdealModule_basisNatTrans i u) V

/-- The additive sheaf comparison intertwines the actual ideal
inclusions into the structure sheaf. -/
theorem openImmersionIdealModule_addSheafHom_toUnit
    {Y Z U : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (u : U ⟶ Y) [IsOpenImmersion u] :
    let iU := pullback.fst u i
    let T := SheafOfModules.toSheaf U.ringCatSheaf
    openImmersionIdealModule_addSheafHom i u ≫
      T.map ((Scheme.Modules.restrictFunctor u).map
        (IdealSheafDataModule.closedImmersionModuleToUnit i)) ≫
      T.map (Scheme.Modules.restrictUnitIso u).hom =
      T.map (IdealSheafDataModule.closedImmersionModuleToUnit iU) := by
  dsimp only
  let B : U.affineOpens → Opens U := fun V => V.1
  have hB : Opens.IsBasis (Set.range B) := by
    simpa [B] using U.isBasis_affineOpens
  apply CategoryTheory.Sheaf.hom_ext
  apply TopCat.Sheaf.hom_ext _ _ hB
  intro V
  ext m
  change (u.appIso V).hom.hom
      ((IdealSheafDataModule.closedImmersionModuleToUnit i).val.app
        (Opposite.op (u ''ᵁ V.1))
        (((openImmersionIdealModule_addSheafHom i u).hom.app
          (Opposite.op V.1)) m)) =
      (IdealSheafDataModule.closedImmersionModuleToUnit
        (pullback.fst u i)).val.app
          (Opposite.op V.1) m
  rw [openImmersionIdealModule_addSheafHom_app_affine]
  have h := openImmersionIdealModule_sectionsEquiv_toUnit i u V m
  have h' := congrArg (u.appIso V).hom.hom h
  change (u.appIso V).hom.hom
      ((IdealSheafDataModule.closedImmersionModuleToUnit i).val.app
        (Opposite.op (u ''ᵁ V.1))
        (openImmersionIdealModule_sectionsEquiv i u V m)) =
      (IdealSheafDataModule.closedImmersionModuleToUnit
        (pullback.fst u i)).val.app
          (Opposite.op V.1) m
  have hcomp (x : Γ(U, V.1)) :
      (u.appIso V).hom.hom
        ((u.appIso V).inv.hom x) = x := by
    have q := ConcreteCategory.congr_hom
      (u.appIso V).inv_hom_id x
    simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using q
  exact h'.symm.trans (hcomp _)

/-- The additive comparison lifts to a morphism of actual ideal-module
sheaves, using the inclusion square to prove linearity on all opens. -/
noncomputable def openImmersionIdealModule_moduleHom
    {Y Z U : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (u : U ⟶ Y) [IsOpenImmersion u] :
    let iU := pullback.fst u i
    IdealSheafDataModule.closedImmersionModule iU ⟶
      (Scheme.Modules.restrictFunctor u).obj
        (IdealSheafDataModule.closedImmersionModule i) := by
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
  let φ := (openImmersionIdealModule_addSheafHom i u).hom
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
  have hs : openImmersionIdealModule_addSheafHom i u ≫ T.map q =
      T.map α := by
    let b := (Scheme.Modules.restrictFunctor u).map
      (IdealSheafDataModule.closedImmersionModuleToUnit i)
    let c := (Scheme.Modules.restrictUnitIso u).hom
    have hmap : T.map (b ≫ c) = T.map b ≫ T.map c := T.map_comp b c
    have hsq : openImmersionIdealModule_addSheafHom i u ≫
        (T.map b ≫ T.map c) = T.map α := by
      simpa only [Category.assoc] using
        openImmersionIdealModule_addSheafHom_toUnit i u
    exact (congrArg (fun t => openImmersionIdealModule_addSheafHom i u ≫ t) hmap).trans hsq
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
theorem openImmersionIdealModule_moduleHom_isIso
    {Y Z U : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (u : U ⟶ Y) [IsOpenImmersion u] :
    IsIso (openImmersionIdealModule_moduleHom i u) := by
  let T := SheafOfModules.toSheaf U.ringCatSheaf
  have hT : IsIso (T.map (openImmersionIdealModule_moduleHom i u)) := by
    change IsIso (openImmersionIdealModule_addSheafHom i u)
    exact openImmersionIdealModule_addSheafHom_isIso i u
  exact (isIso_iff_of_reflects_iso _ T).mp hT

/-- The module-sheaf chart isomorphism, with its actual ideal-module
source and target. -/
noncomputable def openImmersionIdealModule_moduleIso
    {Y Z U : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (u : U ⟶ Y) [IsOpenImmersion u] :
    let iU := pullback.fst u i
    IdealSheafDataModule.closedImmersionModule iU ≅
      (Scheme.Modules.restrictFunctor u).obj
        (IdealSheafDataModule.closedImmersionModule i) := by
  letI := openImmersionIdealModule_moduleHom_isIso i u
  exact asIso (openImmersionIdealModule_moduleHom i u)

/-- The actual ideal-module isomorphism identifies the two inclusion
maps into the structure sheaf on a target chart. -/
theorem openImmersionIdealModule_moduleIso_toUnit
    {Y Z U : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (u : U ⟶ Y) [IsOpenImmersion u] :
    let iU := pullback.fst u i
    (openImmersionIdealModule_moduleIso i u).hom ≫
      (Scheme.Modules.restrictFunctor u).map
        (IdealSheafDataModule.closedImmersionModuleToUnit i) ≫
      (Scheme.Modules.restrictUnitIso u).hom =
        IdealSheafDataModule.closedImmersionModuleToUnit iU := by
  let iU := pullback.fst u i
  let T := SheafOfModules.toSheaf U.ringCatSheaf
  let b := (Scheme.Modules.restrictFunctor u).map
    (IdealSheafDataModule.closedImmersionModuleToUnit i)
  let c := (Scheme.Modules.restrictUnitIso u).hom
  apply T.map_injective
  have h1 := T.map_comp ((openImmersionIdealModule_moduleIso i u).hom ≫ b) c
  have h2 := T.map_comp (openImmersionIdealModule_moduleIso i u).hom b
  have hcomp := h1.trans (congrArg (fun t => t ≫ T.map c) h2)
  have hs := openImmersionIdealModule_addSheafHom_toUnit i u
  exact hcomp.trans hs


end PfaffianDescent
