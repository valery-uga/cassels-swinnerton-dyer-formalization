import PfaffianDescent.VoisinFieldBaseChangeOpenNaturality

namespace PfaffianDescent.BundleSectionZeroLocus

open CategoryTheory AlgebraicGeometry Opposite

universe u

noncomputable section

theorem unitToPushforwardObjUnit_regularFunction
    {X Y : Scheme.{u}} (f : X ⟶ Y) (r : Γ(Y, ⊤)) :
    unitEndomorphismOfRegularFunction (X := Y) r ≫
        SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward f).map
          (unitEndomorphismOfRegularFunction (X := X) (f.appTop r)) := by
  apply ((Scheme.Modules.pushforward f).obj
    (SheafOfModules.unit X.ringCatSheaf)).unitHomEquiv.injective
  erw [SheafOfModules.unitHomEquiv_comp_apply,
    SheafOfModules.unitHomEquiv_comp_apply]
  ext U
  simp only [unitEndomorphismOfRegularFunction, Equiv.apply_symm_apply]
  dsimp only [SheafOfModules.sectionsMap, PresheafOfModules.sectionsMap]
  dsimp only [PresheafOfModules.sectionsMk]
  erw [SheafOfModules.unitToPushforwardObjUnit_val_app_apply]
  erw [SheafOfModules.unitHomEquiv_apply_coe]
  erw [SheafOfModules.unitToPushforwardObjUnit_val_app_apply]
  have hu1 := SheafOfModules.unitToPushforwardObjUnit_val_app_apply
    f.toRingCatSheafHom (X := U) (1 : Y.ringCatSheaf.obj.obj U)
  erw [hu1]
  rw [map_one]
  let sX := unitSectionOfRegularFunction (X := X) (f.appTop r)
  let b := (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm sX
  have hb0 := SheafOfModules.unitHomEquiv_apply_coe
    (SheafOfModules.unit X.ringCatSheaf) b
    ((TopologicalSpace.Opens.map f.base).op.obj U)
  have hb1 := congrArg
    (fun s => s.val ((TopologicalSpace.Opens.map f.base).op.obj U))
    ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.apply_symm_apply sX)
  change f.app U.unop (unitSectionOfRegularFunction (X := Y) r |>.val U) =
    (b.val.app ((TopologicalSpace.Opens.map f.base).op.obj U)).hom _
  erw [← hb0, hb1]
  dsimp only [sX, unitSectionOfRegularFunction, PresheafOfModules.sectionsMk]
  have h := f.naturality
    (homOfLE (show U.unop ≤ ⊤ from le_top)).op
  exact ConcreteCategory.congr_hom h r

theorem pullbackUnitEndomorphismOfRegularFunction_eq_appTop_general
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hunit : IsIso (pullbackUnitComparison f)) (r : Γ(Y, ⊤)) :
    pullbackUnitEndomorphism f hunit
      (unitEndomorphismOfRegularFunction (X := Y) r) =
    unitEndomorphismOfRegularFunction (X := X) (f.appTop r) := by
  let P := Scheme.Modules.pullback f
  let Q := Scheme.Modules.pushforward f
  let A : P ⊣ Q := Scheme.Modules.pullbackPushforwardAdjunction f
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  let p := pullbackUnitComparison f
  let a := unitEndomorphismOfRegularFunction (X := Y) r
  let b := unitEndomorphismOfRegularFunction (X := X) (f.appTop r)
  let u := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  have hpadj : A.homEquiv _ _ p = u := by
    dsimp only [A, p, P, Q, pullbackUnitComparison,
      Scheme.Modules.pullbackPushforwardAdjunction,
      Scheme.Modules.pullback, Scheme.Modules.pushforward, u]
    exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  have hcore : P.map a ≫ p = p ≫ b := by
    apply (A.homEquiv _ _).injective
    have hl : A.homEquiv _ _ (P.map a ≫ p) = a ≫ u :=
      (A.homEquiv_naturality_left a p).trans
        (congrArg (fun z => a ≫ z) hpadj)
    have hr : A.homEquiv _ _ (p ≫ b) = u ≫ Q.map b :=
      (A.homEquiv_naturality_right p b).trans
        (congrArg (fun z => z ≫ Q.map b) hpadj)
    exact hl.trans ((unitToPushforwardObjUnit_regularFunction f r).trans hr.symm)
  let q := Classical.choose hunit.out
  have hqp : q ≫ p = 𝟙 _ := (Classical.choose_spec hunit.out).2
  unfold pullbackUnitEndomorphism
  change q ≫ P.map a ≫ p = b
  erw [hcore, ← Category.assoc, hqp, Category.id_comp]

theorem pullbackFreeIso_inv_comp_freeCoordinateMap
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Type u) [DecidableEq I] {E : Y.Modules}
    (e : SheafOfModules.free (R := Y.ringCatSheaf) I ≅ E) (i : I) :
    (pullbackFreeIso f I e).inv ≫ freeCoordinateMap (X := X) I i =
      (Scheme.Modules.pullback f).map
          (e.inv ≫ freeCoordinateMap (X := Y) I i) ≫
        pullbackUnitComparison f := by
  letI : IsIso (pullbackUnitComparison f) := isIso_pullbackUnitComparison f
  let P := Scheme.Modules.pullback f
  let p := pullbackUnitComparison f
  let q := Classical.choose (isIso_pullbackUnitComparison f).out
  have hqp : q ≫ p = 𝟙 _ :=
    (Classical.choose_spec (isIso_pullbackUnitComparison f).out).2
  let t := pullbackFreeIso f I e
  letI : IsIso t.hom := t.isIso_hom
  letI : Epi t.hom := CategoryTheory.IsIso.epi_of_iso t.hom
  apply (cancel_epi t.hom).1
  apply (SheafOfModules.unit X.ringCatSheaf).freeHomEquiv.injective
  funext j
  apply (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm.injective
  let l := t.hom ≫ t.inv ≫ freeCoordinateMap (X := X) I i
  let r := t.hom ≫ P.map
    (e.inv ≫ freeCoordinateMap (X := Y) I i) ≫ p
  change (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm
      ((SheafOfModules.unit X.ringCatSheaf).freeHomEquiv l j) =
    (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm
      ((SheafOfModules.unit X.ringCatSheaf).freeHomEquiv r j)
  rw [SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply l j,
    SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply r j]
  dsimp only [l, r]
  have hgen : SheafOfModules.ιFree (R := X.ringCatSheaf) j ≫ t.hom =
      q ≫
        P.map (SheafOfModules.ιFree (R := Y.ringCatSheaf) j ≫ e.hom) := by
    exact pullbackFreeIso_ιFree_hom f I e j
  have hdeltaY : SheafOfModules.ιFree (R := Y.ringCatSheaf) j ≫
      freeCoordinateMap (X := Y) I i =
      if j = i then 𝟙 _ else 0 :=
    iota_comp_freeCoordinateMap (X := Y) I i j
  have hdeltaX : SheafOfModules.ιFree (R := X.ringCatSheaf) j ≫
      freeCoordinateMap (X := X) I i =
      if j = i then 𝟙 _ else 0 :=
    iota_comp_freeCoordinateMap (X := X) I i j
  have hright :
      (SheafOfModules.ιFree (R := X.ringCatSheaf) j ≫ t.hom) ≫
          P.map (e.inv ≫ freeCoordinateMap (X := Y) I i) ≫ p =
        q ≫ P.map
          (SheafOfModules.ιFree (R := Y.ringCatSheaf) j ≫
            freeCoordinateMap (X := Y) I i) ≫ p := by
    have hmap : P.map
          (SheafOfModules.ιFree (R := Y.ringCatSheaf) j ≫ e.hom) ≫
        P.map (e.inv ≫ freeCoordinateMap (X := Y) I i) =
        P.map (SheafOfModules.ιFree (R := Y.ringCatSheaf) j ≫
          freeCoordinateMap (X := Y) I i) := by
      have hinside :
          (SheafOfModules.ιFree (R := Y.ringCatSheaf) j ≫ e.hom) ≫
              (e.inv ≫ freeCoordinateMap (X := Y) I i) =
            SheafOfModules.ιFree (R := Y.ringCatSheaf) j ≫
              freeCoordinateMap (X := Y) I i := by
        let g := SheafOfModules.ιFree (R := Y.ringCatSheaf) j
        let c := freeCoordinateMap (X := Y) I i
        have ha := congrArg (fun z => z ≫ c) (Category.assoc g e.hom e.inv)
        have hc := congrArg (fun z => g ≫ z ≫ c) e.hom_inv_id
        have hi := congrArg (fun z => z ≫ c) (Category.comp_id g)
        exact ha.trans (hc.trans (hi.trans (by rfl)))
      exact (P.map_comp _ _).symm.trans (congrArg P.map hinside)
    rw [hgen]
    let A₀ := P.map
      (SheafOfModules.ιFree (R := Y.ringCatSheaf) j ≫ e.hom)
    let B₀ := P.map (e.inv ≫ freeCoordinateMap (X := Y) I i)
    let C₀ := P.map (SheafOfModules.ιFree (R := Y.ringCatSheaf) j ≫
      freeCoordinateMap (X := Y) I i)
    have hmap' : A₀ ≫ B₀ = C₀ := hmap
    have hpre := congrArg (fun z => q ≫ z) hmap'
    exact congrArg (fun z => z ≫ p)
      ((Category.assoc q A₀ B₀).trans hpre)
  have hdelta : SheafOfModules.ιFree (R := X.ringCatSheaf) j ≫
      freeCoordinateMap (X := X) I i =
      q ≫ P.map
        (SheafOfModules.ιFree (R := Y.ringCatSheaf) j ≫
          freeCoordinateMap (X := Y) I i) ≫ p := by
    by_cases hji : j = i
    · subst j
      have hx : SheafOfModules.ιFree (R := X.ringCatSheaf) i ≫
          freeCoordinateMap (X := X) I i = 𝟙 _ :=
        hdeltaX.trans (if_pos rfl)
      have hy : SheafOfModules.ιFree (R := Y.ringCatSheaf) i ≫
          freeCoordinateMap (X := Y) I i = 𝟙 _ :=
        hdeltaY.trans (if_pos rfl)
      have hyr := congrArg (fun z => q ≫ P.map z ≫ p) hy
      have hmid0 := congrArg (fun z => q ≫ z ≫ p)
        (P.map_id (SheafOfModules.unit Y.ringCatSheaf))
      have hmid : q ≫ P.map (𝟙 (SheafOfModules.unit Y.ringCatSheaf)) ≫ p =
          q ≫ p := by
        exact hmid0.trans (congrArg (fun z => z ≫ p) (Category.comp_id q))
      exact hx.trans (hqp.symm.trans (hmid.symm.trans hyr.symm))
    · have hx : SheafOfModules.ιFree (R := X.ringCatSheaf) j ≫
          freeCoordinateMap (X := X) I i = 0 :=
        hdeltaX.trans (if_neg hji)
      have hy : SheafOfModules.ιFree (R := Y.ringCatSheaf) j ≫
          freeCoordinateMap (X := Y) I i = 0 :=
        hdeltaY.trans (if_neg hji)
      have hyr := congrArg (fun z => q ≫ P.map z ≫ p) hy
      have hm0 : P.map (0 : SheafOfModules.unit Y.ringCatSheaf ⟶
          SheafOfModules.unit Y.ringCatSheaf) = 0 := P.map_zero _ _
      have hz0 := congrArg (fun z => q ≫ z ≫ p) hm0
      have hz : q ≫ P.map (0 : SheafOfModules.unit Y.ringCatSheaf ⟶
          SheafOfModules.unit Y.ringCatSheaf) ≫ p =
          (0 : SheafOfModules.unit X.ringCatSheaf ⟶
            SheafOfModules.unit X.ringCatSheaf) := by
        have hq0 := CategoryTheory.Limits.HasZeroMorphisms.comp_zero q
          ((Scheme.Modules.pullback f).obj
            (SheafOfModules.unit Y.ringCatSheaf))
        have hc0 := congrArg (fun z => z ≫ p) hq0
        have h0p := CategoryTheory.Limits.HasZeroMorphisms.zero_comp
          (SheafOfModules.unit X.ringCatSheaf) p
        exact hz0.trans (hc0.trans h0p)
      exact hx.trans (hz.symm.trans hyr.symm)
  have hleft :
      SheafOfModules.ιFree (R := X.ringCatSheaf) j ≫ t.hom ≫ t.inv ≫
          freeCoordinateMap (X := X) I i =
        SheafOfModules.ιFree (R := X.ringCatSheaf) j ≫
          freeCoordinateMap (X := X) I i := by
    let g := SheafOfModules.ιFree (R := X.ringCatSheaf) j
    let c := freeCoordinateMap (X := X) I i
    have ha := congrArg (fun z => z ≫ c) (Category.assoc g t.hom t.inv)
    have hc := congrArg (fun z => g ≫ z ≫ c) t.hom_inv_id
    have hi := congrArg (fun z => z ≫ c) (Category.comp_id g)
    exact ha.trans (hc.trans (hi.trans (by rfl)))
  exact hleft.trans (hdelta.trans hright.symm)

theorem moduleOpenTopLinearEquivOfPullbackFreeIso_general
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Type u) [Fintype I] [DecidableEq I]
    (M : Y.Modules)
    (e : SheafOfModules.free (R := Y.ringCatSheaf) I ≅ M)
    (s : Γ(M, ⊤)) (i : I) :
    let MX := (Scheme.Modules.pullback f).obj M
    let sY := (schemeModuleSectionsEquivTop M).symm s
    let sX := pullbackSection f M
      (isIso_pullbackUnitComparison f) sY
    moduleOpenTopLinearEquivOfFreeIso I MX
        (pullbackFreeIso f I e)
        (schemeModuleSectionsEquivTop MX sX) i =
      f.appTop.hom (moduleOpenTopLinearEquivOfFreeIso I M e s i) := by
  dsimp only
  let P := Scheme.Modules.pullback f
  let MX := P.obj M
  let sY := (schemeModuleSectionsEquivTop M).symm s
  let sX := pullbackSection f M (isIso_pullbackUnitComparison f) sY
  let t := pullbackFreeIso f I e
  rw [moduleOpenTopLinearEquivOfFreeIso_eq_freeSectionCoordinate,
    moduleOpenTopLinearEquivOfFreeIso_eq_freeSectionCoordinate]
  rw [(schemeModuleSectionsEquivTop MX).symm_apply_apply]
  let z := (SheafOfModules.free (R := Y.ringCatSheaf) I).unitHomEquiv.symm
      (SheafOfModules.sectionsMap e.inv sY) ≫
    freeCoordinateMap (X := Y) I i
  let zX := (SheafOfModules.free (R := X.ringCatSheaf) I).unitHomEquiv.symm
      (SheafOfModules.sectionsMap t.inv sX) ≫
    freeCoordinateMap (X := X) I i
  unfold freeSectionCoordinate
  change unitEndomorphismValue (X := X) zX =
    f.appTop (unitEndomorphismValue (X := Y) z)
  have hsec :
      (SheafOfModules.free (R := X.ringCatSheaf) I).unitHomEquiv.symm
          (SheafOfModules.sectionsMap t.inv sX) =
        (P.obj M).unitHomEquiv.symm sX ≫ t.inv := by
    exact (SheafOfModules.unitHomEquiv_symm_comp sX t.inv).symm
  have hsecY :
      (SheafOfModules.free (R := Y.ringCatSheaf) I).unitHomEquiv.symm
          (SheafOfModules.sectionsMap e.inv sY) =
        M.unitHomEquiv.symm sY ≫ e.inv := by
    exact (SheafOfModules.unitHomEquiv_symm_comp sY e.inv).symm
  have hpull : (P.obj M).unitHomEquiv.symm sX =
      Classical.choose (isIso_pullbackUnitComparison f).out ≫
        P.map (M.unitHomEquiv.symm sY) := by
    exact pullbackSection_unitHomEquiv_symm f M
      (isIso_pullbackUnitComparison f) sY
  have hcoord := pullbackFreeIso_inv_comp_freeCoordinateMap f I e i
  have hzX : zX = pullbackUnitEndomorphism f
      (isIso_pullbackUnitComparison f) z := by
    dsimp only [zX, z]
    rw [hsec, hsecY, hpull]
    let q := Classical.choose (isIso_pullbackUnitComparison f).out
    let p := pullbackUnitComparison f
    let m := M.unitHomEquiv.symm sY
    let d := e.inv ≫ freeCoordinateMap (X := Y) I i
    let cX := freeCoordinateMap (X := X) I i
    unfold pullbackUnitEndomorphism
    change ((q ≫ P.map m) ≫ t.inv) ≫ cX =
      q ≫ P.map ((m ≫ e.inv) ≫ freeCoordinateMap (X := Y) I i) ≫ p
    have hc : t.inv ≫ cX = P.map d ≫ p := hcoord
    have hm : P.map m ≫ P.map d = P.map (m ≫ d) :=
      (P.map_comp m d).symm
    have hmd : m ≫ d = (m ≫ e.inv) ≫
        freeCoordinateMap (X := Y) I i :=
      (Category.assoc m e.inv (freeCoordinateMap (X := Y) I i)).symm
    calc
      ((q ≫ P.map m) ≫ t.inv) ≫ cX =
          q ≫ (P.map m ≫ (t.inv ≫ cX)) := by
        have h₁ := congrArg (fun w => w ≫ cX)
          (Category.assoc q (P.map m) t.inv)
        have h₂ := Category.assoc q (P.map m ≫ t.inv) cX
        have h₃ := congrArg (fun w => q ≫ w)
          (Category.assoc (P.map m) t.inv cX)
        exact h₁.trans (h₂.trans h₃)
      _ = q ≫ (P.map m ≫ (P.map d ≫ p)) :=
        congrArg (fun w => q ≫ (P.map m ≫ w)) hc
      _ = q ≫ ((P.map m ≫ P.map d) ≫ p) :=
        congrArg (fun w => q ≫ w) (Category.assoc _ _ _).symm
      _ = q ≫ (P.map (m ≫ d) ≫ p) :=
        congrArg (fun w => q ≫ (w ≫ p)) hm
      _ = q ≫ (P.map ((m ≫ e.inv) ≫
          freeCoordinateMap (X := Y) I i) ≫ p) :=
        congrArg (fun w => q ≫ (P.map w ≫ p)) hmd
      _ = q ≫ P.map ((m ≫ e.inv) ≫
          freeCoordinateMap (X := Y) I i) ≫ p :=
        (Category.assoc _ _ _).symm
  rw [hzX]
  rw [← unitEndomorphismOfRegularFunction_value (X := Y) z]
  rw [pullbackUnitEndomorphismOfRegularFunction_eq_appTop_general]
  rw [unitEndomorphismValue_ofRegularFunction,
    unitEndomorphismValue_ofRegularFunction]

end

end PfaffianDescent.BundleSectionZeroLocus
