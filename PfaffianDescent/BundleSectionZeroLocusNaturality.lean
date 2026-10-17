import PfaffianDescent.BundleSectionZeroLocus
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Naturality of section zero ideals

This module supplies the affine open-restriction calculation required to
assemble zero schemes defined from local free coordinates.
-/

namespace PfaffianDescent.BundleSectionZeroLocus

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/-- On an open immersion, the isomorphism from sections on the image to
sections on the source composes with ordinary restriction to the global
restriction map. -/
theorem appIsoTop_comp_restrict_eq_appTop {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] :
    let e := (f.appIso ⊤).commRingCatIsoToRingEquiv
    e.toRingHom.comp (Y.presheaf.map (homOfLE le_top).op).hom = f.appTop.hom := by
  dsimp
  have hcat : Y.presheaf.map (homOfLE le_top).op ≫ (f.appIso ⊤).hom = f.appTop := by
    rw [Scheme.Hom.appIso_hom']
    rw [Scheme.Hom.map_appLE]
    simpa only [TopologicalSpace.Opens.map_top] using (f.appLE_eq_app (U := ⊤))
  exact congrArg CommRingCat.Hom.hom hcat

/-- Conjugating a scalar endomorphism by the canonical identification of the
restricted structure sheaf transports its global coefficient by ordinary
restriction of functions. -/
theorem unitEndomorphismValue_restrict_eq_appTop {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f]
    (a : SheafOfModules.unit Y.ringCatSheaf ⟶
      SheafOfModules.unit Y.ringCatSheaf) :
    unitEndomorphismValue (X := X)
      ((AlgebraicGeometry.Scheme.Modules.restrictUnitIso f).inv ≫
        (AlgebraicGeometry.Scheme.Modules.restrictFunctor f).map a ≫
        (AlgebraicGeometry.Scheme.Modules.restrictUnitIso f).hom) =
      f.appTop (unitEndomorphismValue (X := Y) a) := by
  unfold unitEndomorphismValue unitSectionAtTop
  change (f.appIso ⊤).hom
      ((a.val.app (Opposite.op (f ''ᵁ ⊤))).hom
        ((f.appIso ⊤).inv (1 : Γ(X, ⊤)))) =
    f.appTop ((a.val.app (Opposite.op ⊤)).hom (1 : Γ(Y, ⊤)))
  rw [map_one]
  let r : Γ(Y, ⊤) →+* Γ(Y, f ''ᵁ ⊤) :=
    (Y.presheaf.map (homOfLE le_top).op).hom
  have hnat := a.val.naturality
    (homOfLE (show f ''ᵁ ⊤ ≤ ⊤ from le_top)).op
  have hnat1 := congrArg (fun q => q.hom (1 : Γ(Y, ⊤))) hnat
  change (f.appIso ⊤).hom
      ((a.val.app (Opposite.op (f ''ᵁ ⊤))).hom (1 : Γ(Y, f ''ᵁ ⊤))) =
    f.appTop ((a.val.app (Opposite.op ⊤)).hom (1 : Γ(Y, ⊤)))
  have hnat' : (a.val.app (Opposite.op (f ''ᵁ ⊤))).hom (r 1) =
      r ((a.val.app (Opposite.op ⊤)).hom (1 : Γ(Y, ⊤))) := by
    exact hnat1
  have hr1 : r 1 = 1 := by simp [r]
  have hnat'' : (a.val.app (Opposite.op (f ''ᵁ ⊤))).hom
      (1 : Γ(Y, f ''ᵁ ⊤)) =
      r ((a.val.app (Opposite.op ⊤)).hom (1 : Γ(Y, ⊤))) := by
    rw [← hr1]
    exact hnat'
  rw [hnat'']
  have hcat : Y.presheaf.map (homOfLE le_top).op ≫
      (f.appIso ⊤).hom = f.appTop := by
    rw [Scheme.Hom.appIso_hom']
    rw [Scheme.Hom.map_appLE]
    simpa only [TopologicalSpace.Opens.map_top] using (f.appLE_eq_app (U := ⊤))
  exact congrArg (fun q : Γ(Y, ⊤) ⟶ Γ(X, ⊤) =>
    q.hom ((a.val.app (Opposite.op ⊤)).hom (1 : Γ(Y, ⊤)))) hcat

/-- Restriction along an open immersion carries multiplication by a regular
function to multiplication by its ordinary restricted function. -/
theorem restrictUnitEndomorphismOfRegularFunction_eq_appTop {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (r : Γ(Y, ⊤)) :
    (AlgebraicGeometry.Scheme.Modules.restrictUnitIso f).inv ≫
      (AlgebraicGeometry.Scheme.Modules.restrictFunctor f).map
        (unitEndomorphismOfRegularFunction (X := Y) r) ≫
      (AlgebraicGeometry.Scheme.Modules.restrictUnitIso f).hom =
    unitEndomorphismOfRegularFunction (X := X) (f.appTop r) := by
  let a : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf :=
    (AlgebraicGeometry.Scheme.Modules.restrictUnitIso f).inv ≫
      (AlgebraicGeometry.Scheme.Modules.restrictFunctor f).map
        (unitEndomorphismOfRegularFunction (X := Y) r) ≫
      (AlgebraicGeometry.Scheme.Modules.restrictUnitIso f).hom
  change a = unitEndomorphismOfRegularFunction (X := X) (f.appTop r)
  calc
    a = unitEndomorphismOfRegularFunction (X := X)
        (unitEndomorphismValue (X := X) a) :=
      (unitEndomorphismOfRegularFunction_value a).symm
    _ = unitEndomorphismOfRegularFunction (X := X) (f.appTop r) := by
      congr 1
      dsimp [a]
      rw [unitEndomorphismValue_restrict_eq_appTop]
      exact congrArg f.appTop (unitEndomorphismValue_ofRegularFunction r)

/-- The canonical map from the unit module to its pushforward along an open
immersion is the restriction-adjunction unit followed by the identification
of the restricted unit module with the source unit module. -/
theorem unitToPushforwardObjUnit_eq_restrictAdjunction {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] :
    SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom =
      (AlgebraicGeometry.Scheme.Modules.restrictAdjunction f).unit.app
        (SheafOfModules.unit Y.ringCatSheaf) ≫
      (AlgebraicGeometry.Scheme.Modules.pushforward f).map
        (AlgebraicGeometry.Scheme.Modules.restrictUnitIso f).hom := by
  apply AlgebraicGeometry.Scheme.Modules.hom_ext
  intro U
  change AlgebraicGeometry.Scheme.Modules.Hom.app
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) U =
    AlgebraicGeometry.Scheme.Modules.Hom.app
      ((AlgebraicGeometry.Scheme.Modules.restrictAdjunction f).unit.app
        (SheafOfModules.unit Y.ringCatSheaf)) U ≫
      AlgebraicGeometry.Scheme.Modules.Hom.app
        ((AlgebraicGeometry.Scheme.Modules.pushforward f).map
          (AlgebraicGeometry.Scheme.Modules.restrictUnitIso f).hom) U
  ext x
  have hmap := AlgebraicGeometry.Scheme.Modules.pushforward_map_app
    (f := f) (φ := (AlgebraicGeometry.Scheme.Modules.restrictUnitIso f).hom) U
  have hB := AlgebraicGeometry.Scheme.Modules.restrictAdjunction_unit_app_app f
    (SheafOfModules.unit Y.ringCatSheaf) U
  have hBx := congrArg (fun z => z.hom x) hB
  change f.app U x =
    ((AlgebraicGeometry.Scheme.Modules.restrictUnitIso f).hom.app (f ⁻¹ᵁ U))
      (((AlgebraicGeometry.Scheme.Modules.restrictAdjunction f).unit.app
        (SheafOfModules.unit Y.ringCatSheaf)).app U x)
  rw [hBx]
  change f.app U x =
    (f.appIso (f ⁻¹ᵁ U)).hom
      (Y.presheaf.map (homOfLE (f.image_preimage_le U)).op x)
  change Γ(Y, U) at x
  have h₁ := congrArg (fun z => z.hom x) (f.app_appIso_inv U)
  have h₂ := congrArg (fun z => (f.appIso (f ⁻¹ᵁ U)).hom z) h₁
  have hleft :
      (f.appIso (f ⁻¹ᵁ U)).hom
        ((f.app U ≫ (f.appIso (f ⁻¹ᵁ U)).inv).hom x) = f.app U x := by
    change (f.appIso (f ⁻¹ᵁ U)).hom
      ((f.appIso (f ⁻¹ᵁ U)).inv ((f.app U).hom x)) = (f.app U).hom x
    exact congrArg (fun z => z.hom ((f.app U).hom x))
      (f.appIso (f ⁻¹ᵁ U)).inv_hom_id
  rw [hleft] at h₂
  exact h₂

/-- On an open immersion, the canonical pullback comparison for the unit
module is the comparison induced from restriction of sheaves. -/
theorem pullbackUnitComparison_eq_restrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] :
    pullbackUnitComparison f =
      (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback f).inv.app
        (SheafOfModules.unit Y.ringCatSheaf) ≫
      (AlgebraicGeometry.Scheme.Modules.restrictUnitIso f).hom := by
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  let A : AlgebraicGeometry.Scheme.Modules.pullback f ⊣
      AlgebraicGeometry.Scheme.Modules.pushforward f :=
    AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f
  let B := AlgebraicGeometry.Scheme.Modules.restrictAdjunction f
  let e := B.leftAdjointUniq A
  change pullbackUnitComparison f = e.inv.app
      (SheafOfModules.unit Y.ringCatSheaf) ≫
    (AlgebraicGeometry.Scheme.Modules.restrictUnitIso f).hom
  apply (A.homEquiv _ _).injective
  have hpc : A.homEquiv _ _ (pullbackUnitComparison f) =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
    unfold pullbackUnitComparison
    exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  rw [hpc]
  change SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom =
    A.homEquiv _ _ (e.inv.app _ ≫
      (AlgebraicGeometry.Scheme.Modules.restrictUnitIso f).hom)
  change SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom =
    A.unit.app _ ≫
      (AlgebraicGeometry.Scheme.Modules.pushforward f).map
        (e.inv.app _ ≫ (AlgebraicGeometry.Scheme.Modules.restrictUnitIso f).hom)
  have hunit := B.unit_leftAdjointUniq_hom_app A
    (SheafOfModules.unit Y.ringCatSheaf)
  rw [unitToPushforwardObjUnit_eq_restrictAdjunction]
  erw [Functor.map_comp]
  rw [← hunit]
  let F := AlgebraicGeometry.Scheme.Modules.pushforward f
  let q := e.hom.app (SheafOfModules.unit Y.ringCatSheaf)
  let r := e.inv.app (SheafOfModules.unit Y.ringCatSheaf)
  let s := (AlgebraicGeometry.Scheme.Modules.restrictUnitIso f).hom
  have hqr : F.map q ≫ F.map r = 𝟙 _ := by
    change F.map (e.hom.app _ ≫ e.inv.app _) = 𝟙 _
    calc
      F.map (e.hom.app _ ≫ e.inv.app _) = F.map (𝟙 _) :=
        congrArg F.map (e.hom_inv_id_app _)
      _ = 𝟙 _ := F.map_id _
  change B.unit.app _ ≫ F.map s =
    B.unit.app _ ≫ F.map q ≫ F.map r ≫ F.map s
  symm
  calc
    B.unit.app _ ≫ F.map q ≫ F.map r ≫ F.map s =
        B.unit.app _ ≫ ((F.map q ≫ F.map r) ≫ F.map s) := by
      simp only [Category.assoc]
    _ = B.unit.app _ ≫ (𝟙 _ ≫ F.map s) := by
      exact congrArg (fun z => B.unit.app _ ≫ (z ≫ F.map s)) hqr
    _ = B.unit.app _ ≫ F.map s := by simp

noncomputable def restrictModuleSection {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (E : Y.Modules) (s : E.sections) :
    ((AlgebraicGeometry.Scheme.Modules.restrictFunctor f).obj E).sections :=
  ((AlgebraicGeometry.Scheme.Modules.restrictFunctor f).obj E).unitHomEquiv
    ((AlgebraicGeometry.Scheme.Modules.restrictUnitIso f).symm.hom ≫
      (AlgebraicGeometry.Scheme.Modules.restrictFunctor f).map
        (E.unitHomEquiv.symm s))

/-- On an open immersion, canonical restriction of a section agrees with the
section obtained by pullback, after the canonical comparison between
restriction and pullback modules. -/
theorem restrictModuleSection_to_pullbackSection
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {E : Y.Modules} (hunit : IsIso (pullbackUnitComparison f))
    (s : E.sections) :
    SheafOfModules.sectionsMap
      ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback f).hom.app E)
      (restrictModuleSection f E s) =
    pullbackSection f E hunit s := by
  letI : IsIso (pullbackUnitComparison f) := hunit
  apply ((AlgebraicGeometry.Scheme.Modules.pullback f).obj E).unitHomEquiv.symm.injective
  erw [← ((AlgebraicGeometry.Scheme.Modules.restrictFunctor f).obj E).unitHomEquiv_symm_comp
    (restrictModuleSection f E s)
    ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback f).hom.app E)]
  unfold restrictModuleSection
  rw [Equiv.symm_apply_apply, pullbackSection_unitHomEquiv_symm_eq_inv]
  let α := AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback f
  let ρ := AlgebraicGeometry.Scheme.Modules.restrictUnitIso f
  have hcomp : pullbackUnitComparison f = α.inv.app _ ≫ ρ.hom :=
    pullbackUnitComparison_eq_restrict f
  have hinv : inv (pullbackUnitComparison f) =
      ρ.inv ≫ α.hom.app (SheafOfModules.unit Y.ringCatSheaf) := by
    apply (IsIso.eq_inv_of_hom_inv_id (by
      rw [hcomp]
      calc
        (α.inv.app _ ≫ ρ.hom) ≫ (ρ.inv ≫ α.hom.app _) =
            α.inv.app _ ≫ (ρ.hom ≫ ρ.inv) ≫ α.hom.app _ := by
          rfl
        _ = α.inv.app _ ≫ (𝟙 _ ≫ α.hom.app _) := by
          exact congrArg (fun z => α.inv.app _ ≫ (z ≫ α.hom.app _)) ρ.hom_inv_id
        _ = α.inv.app _ ≫ α.hom.app _ := by rw [Category.id_comp]
        _ = 𝟙 _ := α.inv_hom_id_app _)).symm
  rw [hinv]
  calc
    ((AlgebraicGeometry.Scheme.Modules.restrictUnitIso f).symm.hom ≫
        (AlgebraicGeometry.Scheme.Modules.restrictFunctor f).map
          (E.unitHomEquiv.symm s)) ≫
        (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback f).hom.app E =
      ρ.symm.hom ≫ ((AlgebraicGeometry.Scheme.Modules.restrictFunctor f).map
        (E.unitHomEquiv.symm s) ≫ α.hom.app E) := by
        rfl
    _ = ρ.symm.hom ≫ (α.hom.app (SheafOfModules.unit Y.ringCatSheaf) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback f).map (E.unitHomEquiv.symm s)) := by
        exact congrArg (fun q => ρ.symm.hom ≫ q)
          (α.hom.naturality (E.unitHomEquiv.symm s))
    _ = (ρ.symm.hom ≫ α.hom.app (SheafOfModules.unit Y.ringCatSheaf)) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback f).map (E.unitHomEquiv.symm s) :=
      (Category.assoc _ _ _).symm

/-- Transporting a restricted section through a target isomorphism can be
computed by first identifying restriction with pullback. -/
theorem sectionsMap_restrictModuleSection_eq_pullbackSection
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {E : Y.Modules} (hunit : IsIso (pullbackUnitComparison f))
    {F : X.Modules}
    (a : (Scheme.Modules.restrictFunctor f).obj E ≅ F)
    (s : E.sections) :
    SheafOfModules.sectionsMap a.hom (restrictModuleSection f E s) =
      SheafOfModules.sectionsMap
        (((Scheme.Modules.restrictFunctorIsoPullback f).app E).symm ≪≫ a).hom
        (pullbackSection f E hunit s) := by
  let α := (Scheme.Modules.restrictFunctorIsoPullback f).app E
  let r := restrictModuleSection f E s
  let p := pullbackSection f E hunit s
  have hp : SheafOfModules.sectionsMap α.hom r = p :=
    restrictModuleSection_to_pullbackSection f hunit s
  have hr : r = SheafOfModules.sectionsMap α.inv p := by
    calc
      r = SheafOfModules.sectionsMap (𝟙 _) r :=
        (SheafOfModules.sectionsMap_id r).symm
      _ = SheafOfModules.sectionsMap (α.hom ≫ α.inv) r :=
        congrArg (fun q => SheafOfModules.sectionsMap q r) α.hom_inv_id.symm
      _ = SheafOfModules.sectionsMap α.inv
          (SheafOfModules.sectionsMap α.hom r) :=
        SheafOfModules.sectionsMap_comp α.hom α.inv r
      _ = SheafOfModules.sectionsMap α.inv p :=
        congrArg (SheafOfModules.sectionsMap α.inv) hp
  change SheafOfModules.sectionsMap a.hom r =
    SheafOfModules.sectionsMap (α.inv ≫ a.hom) p
  rw [hr]
  exact (SheafOfModules.sectionsMap_comp α.inv a.hom p).symm

/-- Two successive target transports after restriction may likewise be
computed after replacing restriction by pullback. -/
theorem sectionsMap₂_restrictModuleSection_eq_pullbackSection
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {E : Y.Modules} (hunit : IsIso (pullbackUnitComparison f))
    {F G : X.Modules}
    (a : (Scheme.Modules.restrictFunctor f).obj E ≅ F)
    (b : F ≅ G) (s : E.sections) :
    SheafOfModules.sectionsMap b.hom
        (SheafOfModules.sectionsMap a.hom (restrictModuleSection f E s)) =
      SheafOfModules.sectionsMap
        ((((Scheme.Modules.restrictFunctorIsoPullback f).app E).symm ≪≫ a) ≪≫ b).hom
        (pullbackSection f E hunit s) := by
  calc
    SheafOfModules.sectionsMap b.hom
        (SheafOfModules.sectionsMap a.hom (restrictModuleSection f E s)) =
      SheafOfModules.sectionsMap (a.hom ≫ b.hom)
        (restrictModuleSection f E s) :=
      (SheafOfModules.sectionsMap_comp a.hom b.hom _).symm
    _ = SheafOfModules.sectionsMap
        (((Scheme.Modules.restrictFunctorIsoPullback f).app E).symm ≪≫
          (a ≪≫ b)).hom (pullbackSection f E hunit s) :=
      sectionsMap_restrictModuleSection_eq_pullbackSection
        f hunit (a ≪≫ b) s
    _ = _ := rfl

/-- Applying the inverse and then the forward map of a module isomorphism
recovers a section. -/
theorem sectionsMap_hom_inv {X : Scheme.{u}} {M N : SheafOfModules X.ringCatSheaf}
    (e : M ≅ N) (s : N.sections) :
    SheafOfModules.sectionsMap e.hom (SheafOfModules.sectionsMap e.inv s) = s := by
  calc
    SheafOfModules.sectionsMap e.hom (SheafOfModules.sectionsMap e.inv s) =
        SheafOfModules.sectionsMap (e.inv ≫ e.hom) s :=
      (SheafOfModules.sectionsMap_comp e.inv e.hom s).symm
    _ = SheafOfModules.sectionsMap (𝟙 _) s :=
      congrArg (fun h => SheafOfModules.sectionsMap h s) e.inv_hom_id
    _ = s := SheafOfModules.sectionsMap_id s

/-- Pulling back multiplication by a regular function along an open immersion
is multiplication by the ordinary restricted regular function. -/
theorem pullbackUnitEndomorphismOfRegularFunction_eq_appTop {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f]
    (hunit : IsIso (pullbackUnitComparison f)) (r : Γ(Y, ⊤)) :
    pullbackUnitEndomorphism f hunit
      (unitEndomorphismOfRegularFunction (X := Y) r) =
    unitEndomorphismOfRegularFunction (X := X) (f.appTop r) := by
  letI : IsIso (pullbackUnitComparison f) := hunit
  let A : AlgebraicGeometry.Scheme.Modules.pullback f ⊣
      AlgebraicGeometry.Scheme.Modules.pushforward f :=
    AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f
  let B := AlgebraicGeometry.Scheme.Modules.restrictAdjunction f
  let e := B.leftAdjointUniq A
  let R := AlgebraicGeometry.Scheme.Modules.restrictFunctor f
  let P := AlgebraicGeometry.Scheme.Modules.pullback f
  let u := AlgebraicGeometry.Scheme.Modules.restrictUnitIso f
  let a := unitEndomorphismOfRegularFunction (X := Y) r
  have hcomparison : pullbackUnitComparison f = e.inv.app _ ≫ u.hom :=
    pullbackUnitComparison_eq_restrict f
  have hinv : inv (pullbackUnitComparison f) = u.inv ≫ e.hom.app _ := by
    apply (IsIso.eq_inv_of_hom_inv_id (by
      rw [hcomparison]
      calc
        (e.inv.app _ ≫ u.hom) ≫ (u.inv ≫ e.hom.app _) =
            e.inv.app _ ≫ (u.hom ≫ u.inv) ≫ e.hom.app _ := by
          rfl
        _ = e.inv.app _ ≫ (𝟙 _ ≫ e.hom.app _) := by
          exact congrArg (fun z => e.inv.app _ ≫ (z ≫ e.hom.app _)) u.hom_inv_id
        _ = e.inv.app _ ≫ e.hom.app _ := by
          rw [Category.id_comp]
        _ = 𝟙 _ := e.inv_hom_id_app _)).symm
  have hnatural := e.hom.naturality a
  have hmiddle : e.hom.app _ ≫ P.map a ≫ e.inv.app _ = R.map a := by
    calc
      e.hom.app _ ≫ P.map a ≫ e.inv.app _ =
          (e.hom.app _ ≫ P.map a) ≫ e.inv.app _ :=
        (Category.assoc _ _ _).symm
      _ = (R.map a ≫ e.hom.app _) ≫ e.inv.app _ :=
        congrArg (fun z => z ≫ e.inv.app _) hnatural.symm
      _ = R.map a ≫ e.hom.app _ ≫ e.inv.app _ := Category.assoc _ _ _
      _ = R.map a ≫ 𝟙 _ :=
        congrArg (fun z => R.map a ≫ z) (e.hom_inv_id_app _)
      _ = R.map a := Category.comp_id _
  have hpullback : pullbackUnitEndomorphism f hunit a =
      u.inv ≫ R.map a ≫ u.hom := by
    unfold pullbackUnitEndomorphism
    have hchoose : Classical.choose hunit.out = inv (pullbackUnitComparison f) := by
      congr 1
    erw [hchoose]
    rw [hinv, hcomparison]
    change (u.inv ≫ e.hom.app _) ≫ P.map a ≫ (e.inv.app _ ≫ u.hom) =
      u.inv ≫ R.map a ≫ u.hom
    calc
      (u.inv ≫ e.hom.app _) ≫ P.map a ≫ e.inv.app _ ≫ u.hom =
          u.inv ≫ (e.hom.app _ ≫ P.map a ≫ e.inv.app _) ≫ u.hom := by
        rfl
      _ = u.inv ≫ R.map a ≫ u.hom := by
        exact congrArg (fun z => u.inv ≫ z ≫ u.hom) hmiddle
  rw [hpullback]
  exact restrictUnitEndomorphismOfRegularFunction_eq_appTop f r

private lemma restriction_iso_hom_map_id_inv {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A : C} {B : D} (e : B ≅ F.obj A) :
    𝟙 B = e.hom ≫ F.map (𝟙 A) ≫ e.inv := by
  simp

private lemma restriction_iso_hom_map_zero_inv {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D)
    [F.PreservesZeroMorphisms] {A : C} {B : D} (e : B ≅ F.obj A) :
    (0 : B ⟶ B) = e.hom ≫ F.map (0 : A ⟶ A) ≫ e.inv := by
  simp
noncomputable def restrictionFreeIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (I : Type u) :
    SheafOfModules.free (R := X.ringCatSheaf) I ≅
      (AlgebraicGeometry.Scheme.Modules.restrictFunctor f).obj
        (SheafOfModules.free (R := Y.ringCatSheaf) I) := by
  let F := AlgebraicGeometry.Scheme.Modules.restrictFunctor f
  letI hpres : PreservesColimitsOfShape (Discrete I) F :=
    (AlgebraicGeometry.Scheme.Modules.restrictAdjunction f).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  exact @SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ F I hpres
    (AlgebraicGeometry.Scheme.Modules.restrictUnitIso f).symm
noncomputable def restrictionFreeIsoOf {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] {E : Y.Modules} (I : Type u)
    (e : SheafOfModules.free (R := Y.ringCatSheaf) I ≅ E) :
    SheafOfModules.free (R := X.ringCatSheaf) I ≅
      (AlgebraicGeometry.Scheme.Modules.restrictFunctor f).obj E :=
  restrictionFreeIso f I ≪≫
    (AlgebraicGeometry.Scheme.Modules.restrictFunctor f).mapIso e

/-- The pulled-back free frame sends a free generator to the pullback of
the corresponding generator, preceded by the inverse unit comparison. -/
theorem pullbackFreeIso_ιFree_hom
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso (pullbackUnitComparison f)]
    {E : Y.Modules} (I : Type u)
    (e : SheafOfModules.free (R := Y.ringCatSheaf) I ≅ E)
    (i : I) :
    SheafOfModules.ιFree i ≫ (pullbackFreeIso f I e).hom =
      inv (pullbackUnitComparison f) ≫
        (Scheme.Modules.pullback f).map
          (SheafOfModules.ιFree i ≫ e.hom) := by
  letI : (TopologicalSpace.Opens.map f.base).Final := opensMap_final f
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  letI : IsIso
      (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) := by
    change IsIso (pullbackUnitComparison f)
    infer_instance
  unfold pullbackFreeIso
  erw [Iso.trans_hom]
  erw [Functor.map_comp]
  erw [← Category.assoc]
  change (SheafOfModules.ιFree i ≫
      (SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I).inv) ≫
      (Scheme.Modules.pullback f).map e.hom =
    (inv (pullbackUnitComparison f) ≫
      (Scheme.Modules.pullback f).map (SheafOfModules.ιFree i)) ≫
      (Scheme.Modules.pullback f).map e.hom
  have hgen : SheafOfModules.ιFree i ≫
        (SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I).inv =
      inv (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
        (Scheme.Modules.pullback f).map (SheafOfModules.ιFree i) := by
    have hmap :
        (Scheme.Modules.pullback f).map (SheafOfModules.ιFree i) ≫
            (SheafOfModules.pullbackObjFreeIso
              f.toRingCatSheafHom I).hom =
          SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom ≫
            SheafOfModules.ιFree i := by
      exact SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom
        (φ := f.toRingCatSheafHom) i
    apply (cancel_mono
      (SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I).hom).1
    calc
      (SheafOfModules.ιFree i ≫
          (SheafOfModules.pullbackObjFreeIso
            f.toRingCatSheafHom I).inv) ≫
          (SheafOfModules.pullbackObjFreeIso
            f.toRingCatSheafHom I).hom =
          SheafOfModules.ιFree i := by simp
      _ = inv (SheafOfModules.pullbackObjUnitToUnit
              f.toRingCatSheafHom) ≫
            SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom ≫
              SheafOfModules.ιFree i := by simp
      _ = inv (SheafOfModules.pullbackObjUnitToUnit
              f.toRingCatSheafHom) ≫
            ((Scheme.Modules.pullback f).map (SheafOfModules.ιFree i) ≫
              (SheafOfModules.pullbackObjFreeIso
                f.toRingCatSheafHom I).hom) :=
          congrArg (fun z =>
            inv (SheafOfModules.pullbackObjUnitToUnit
              f.toRingCatSheafHom) ≫ z) hmap.symm
      _ = (inv (SheafOfModules.pullbackObjUnitToUnit
              f.toRingCatSheafHom) ≫
            (Scheme.Modules.pullback f).map (SheafOfModules.ιFree i)) ≫
              (SheafOfModules.pullbackObjFreeIso
                f.toRingCatSheafHom I).hom :=
          (Category.assoc _ _ _).symm
  change (SheafOfModules.ιFree i ≫
      (SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I).inv) ≫
      (Scheme.Modules.pullback f).map e.hom =
    (inv (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
      (Scheme.Modules.pullback f).map (SheafOfModules.ιFree i)) ≫
      (Scheme.Modules.pullback f).map e.hom
  rw [hgen]
  rfl

/-- On sections, the generator of a pulled-back free frame is the pullback
of the corresponding generator section. -/
theorem pullbackFreeIso_ιFree_section
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso (pullbackUnitComparison f)]
    {E : Y.Modules} (I : Type u)
    (e : SheafOfModules.free (R := Y.ringCatSheaf) I ≅ E)
    (i : I) :
    ((Scheme.Modules.pullback f).obj E).unitHomEquiv
        (SheafOfModules.ιFree i ≫ (pullbackFreeIso f I e).hom) =
      pullbackSection f E (by infer_instance)
        (E.unitHomEquiv (SheafOfModules.ιFree i ≫ e.hom)) := by
  apply ((Scheme.Modules.pullback f).obj E).unitHomEquiv.symm.injective
  rw [Equiv.symm_apply_apply]
  rw [pullbackSection_unitHomEquiv_symm_eq_inv]
  rw [Equiv.symm_apply_apply]
  exact pullbackFreeIso_ιFree_hom f I e i

/-- Restricting a free frame sends a free generator to the restriction of
the corresponding generator, preceded by the inverse restriction-unit map. -/
theorem restrictionFreeIsoOf_ιFree_hom
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {E : Y.Modules} (I : Type u)
    (e : SheafOfModules.free (R := Y.ringCatSheaf) I ≅ E)
    (i : I) :
    SheafOfModules.ιFree i ≫ (restrictionFreeIsoOf f I e).hom =
      (Scheme.Modules.restrictUnitIso f).inv ≫
        (Scheme.Modules.restrictFunctor f).map
          (SheafOfModules.ιFree i ≫ e.hom) := by
  letI hpres : PreservesColimitsOfShape (Discrete I)
      (Scheme.Modules.restrictFunctor f) :=
    (Scheme.Modules.restrictAdjunction f).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  unfold restrictionFreeIsoOf
  unfold restrictionFreeIso
  erw [Iso.trans_hom]
  erw [Functor.map_comp]
  erw [← Category.assoc]
  rw [@SheafOfModules.ιFree_mapFreeIso_hom
    _ _ _ _ _ _ _ _ _ _ _ _
    (Scheme.Modules.restrictFunctor f) I hpres
    (Scheme.Modules.restrictUnitIso f).symm i]
  exact Category.assoc _ _ _

/-- On sections, the generator of a restricted free frame is the ordinary
restriction of the corresponding generator section. -/
theorem restrictionFreeIsoOf_ιFree_section
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {E : Y.Modules} (I : Type u)
    (e : SheafOfModules.free (R := Y.ringCatSheaf) I ≅ E)
    (i : I) :
    ((Scheme.Modules.restrictFunctor f).obj E).unitHomEquiv
        (SheafOfModules.ιFree i ≫ (restrictionFreeIsoOf f I e).hom) =
      restrictModuleSection f E
        (E.unitHomEquiv (SheafOfModules.ιFree i ≫ e.hom)) := by
  apply ((Scheme.Modules.restrictFunctor f).obj E).unitHomEquiv.symm.injective
  rw [Equiv.symm_apply_apply]
  unfold restrictModuleSection
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact restrictionFreeIsoOf_ιFree_hom f I e i

/-- Evaluating a generator after a composite frame is the same as mapping
its section through the second frame isomorphism. -/
theorem unitHomEquiv_ιFree_trans
    {X : Scheme.{u}} {E F : X.Modules} (I : Type u)
    (e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ E)
    (a : E ≅ F) (i : I) :
    F.unitHomEquiv (SheafOfModules.ιFree i ≫ (e ≪≫ a).hom) =
      SheafOfModules.sectionsMap a.hom
        (E.unitHomEquiv (SheafOfModules.ιFree i ≫ e.hom)) := by
  apply F.unitHomEquiv.symm.injective
  rw [Equiv.symm_apply_apply]
  have h := E.unitHomEquiv_symm_comp
    (E.unitHomEquiv (SheafOfModules.ιFree i ≫ e.hom)) a.hom
  rw [Equiv.symm_apply_apply] at h
  change (SheafOfModules.ιFree i ≫ e.hom) ≫ a.hom = _
  exact h

theorem restrictionFreeIso_inv_comp_freeCoordinateMap {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (I : Type u)
    [DecidableEq I] (i : I) :
    (restrictionFreeIso f I).inv ≫ freeCoordinateMap (X := X) I i =
      (AlgebraicGeometry.Scheme.Modules.restrictFunctor f).map
        (freeCoordinateMap (X := Y) I i) ≫
        (AlgebraicGeometry.Scheme.Modules.restrictUnitIso f).hom := by
  unfold restrictionFreeIso
  let F := AlgebraicGeometry.Scheme.Modules.restrictFunctor f
  letI hpres : PreservesColimitsOfShape (Discrete I) F :=
    (AlgebraicGeometry.Scheme.Modules.restrictAdjunction f).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  let η := (AlgebraicGeometry.Scheme.Modules.restrictUnitIso f).symm
  let e := @SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ F I hpres η
  change e.inv ≫ freeCoordinateMap (X := X) I i = _
  apply (cancel_epi e.hom).1
  apply (SheafOfModules.unit X.ringCatSheaf).freeHomEquiv.injective
  funext j
  apply (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm.injective
  let l : SheafOfModules.free (R := X.ringCatSheaf) I ⟶
      SheafOfModules.unit X.ringCatSheaf :=
    e.hom ≫ e.inv ≫ freeCoordinateMap (X := X) I i
  let r : SheafOfModules.free (R := X.ringCatSheaf) I ⟶
      SheafOfModules.unit X.ringCatSheaf :=
    e.hom ≫ F.map (freeCoordinateMap (X := Y) I i) ≫
      (AlgebraicGeometry.Scheme.Modules.restrictUnitIso f).hom
  change (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm
      ((SheafOfModules.unit X.ringCatSheaf).freeHomEquiv l j) =
    (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm
      ((SheafOfModules.unit X.ringCatSheaf).freeHomEquiv r j)
  rw [SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply l j,
    SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply r j]
  dsimp [l, r]
  have hmap : SheafOfModules.ιFree (R := X.ringCatSheaf) j ≫ e.hom =
      η.hom ≫ F.map (SheafOfModules.ιFree (R := Y.ringCatSheaf) j) := by
    exact @SheafOfModules.ιFree_mapFreeIso_hom _ _ _ _ _ _ _ _ _ _ _ _
      F I hpres η j
  have hcomp :
      (η.hom ≫ F.map (SheafOfModules.ιFree (R := Y.ringCatSheaf) j) ≫
        F.map (freeCoordinateMap (X := Y) I i)) ≫ η.inv =
      η.hom ≫ F.map
        (SheafOfModules.ιFree (R := Y.ringCatSheaf) j ≫
          freeCoordinateMap (X := Y) I i) ≫ η.inv := by
    calc
      (η.hom ≫ F.map (SheafOfModules.ιFree (R := Y.ringCatSheaf) j) ≫
          F.map (freeCoordinateMap (X := Y) I i)) ≫ η.inv =
          (η.hom ≫ F.map (SheafOfModules.ιFree (R := Y.ringCatSheaf) j)) ≫
            (F.map (freeCoordinateMap (X := Y) I i) ≫ η.inv) :=
        Category.assoc _ _ _
      _ = η.hom ≫ (F.map (SheafOfModules.ιFree (R := Y.ringCatSheaf) j) ≫
            (F.map (freeCoordinateMap (X := Y) I i) ≫ η.inv)) :=
        Category.assoc _ _ _
      _ = η.hom ≫ ((F.map (SheafOfModules.ιFree (R := Y.ringCatSheaf) j) ≫
            F.map (freeCoordinateMap (X := Y) I i)) ≫ η.inv) := by
        exact congrArg (fun q => η.hom ≫ q) (Category.assoc _ _ _).symm
      _ = η.hom ≫ (F.map
            (SheafOfModules.ιFree (R := Y.ringCatSheaf) j ≫
              freeCoordinateMap (X := Y) I i) ≫ η.inv) := by
        exact congrArg (fun q => η.hom ≫ (q ≫ η.inv))
          (F.map_comp _ _).symm
      _ = η.hom ≫ F.map
            (SheafOfModules.ιFree (R := Y.ringCatSheaf) j ≫
              freeCoordinateMap (X := Y) I i) ≫ η.inv :=
        (Category.assoc _ _ _).symm
  have hdeltaY : SheafOfModules.ιFree (R := Y.ringCatSheaf) j ≫
      freeCoordinateMap (X := Y) I i =
      if j = i then 𝟙 _ else 0 :=
    iota_comp_freeCoordinateMap (X := Y) I i j
  have hdeltaX : SheafOfModules.ιFree (R := X.ringCatSheaf) j ≫
      freeCoordinateMap (X := X) I i =
      if j = i then 𝟙 _ else 0 :=
    iota_comp_freeCoordinateMap (X := X) I i j
  have hdeltaYF :
      η.hom ≫ F.map
          (SheafOfModules.ιFree (R := Y.ringCatSheaf) j ≫
            freeCoordinateMap (X := Y) I i) ≫ η.inv =
        η.hom ≫ F.map
          (if j = i then 𝟙 (SheafOfModules.unit Y.ringCatSheaf) else
            (0 : SheafOfModules.unit Y.ringCatSheaf ⟶
              SheafOfModules.unit Y.ringCatSheaf)) ≫ η.inv := by
    exact congrArg (fun q : SheafOfModules.unit Y.ringCatSheaf ⟶
        SheafOfModules.unit Y.ringCatSheaf => η.hom ≫ F.map q ≫ η.inv) hdeltaY
  have hdelta : SheafOfModules.ιFree (R := X.ringCatSheaf) j ≫
      freeCoordinateMap (X := X) I i =
      η.hom ≫ F.map
        (SheafOfModules.ιFree (R := Y.ringCatSheaf) j ≫
          freeCoordinateMap (X := Y) I i) ≫ η.inv := by
    by_cases hji : j = i
    · subst j
      have hleft :
          (if i = i then 𝟙 (SheafOfModules.unit X.ringCatSheaf) else
            (0 : SheafOfModules.unit X.ringCatSheaf ⟶
              SheafOfModules.unit X.ringCatSheaf)) = 𝟙 _ := if_pos rfl
      have hif :
          (if i = i then 𝟙 (SheafOfModules.unit Y.ringCatSheaf) else
            (0 : SheafOfModules.unit Y.ringCatSheaf ⟶
              SheafOfModules.unit Y.ringCatSheaf)) = 𝟙 _ := if_pos rfl
      have hifF := congrArg
        (fun q : SheafOfModules.unit Y.ringCatSheaf ⟶
            SheafOfModules.unit Y.ringCatSheaf => η.hom ≫ F.map q ≫ η.inv) hif
      have hmid : 𝟙 (SheafOfModules.unit X.ringCatSheaf) = η.hom ≫ F.map
          (if i = i then 𝟙 (SheafOfModules.unit Y.ringCatSheaf) else
            (0 : SheafOfModules.unit Y.ringCatSheaf ⟶
              SheafOfModules.unit Y.ringCatSheaf)) ≫ η.inv :=
        (restriction_iso_hom_map_id_inv F η).trans hifF.symm
      exact ((hdeltaX.trans hleft).trans hmid).trans hdeltaYF.symm
    · have hleft :
          (if j = i then 𝟙 (SheafOfModules.unit X.ringCatSheaf) else
            (0 : SheafOfModules.unit X.ringCatSheaf ⟶
              SheafOfModules.unit X.ringCatSheaf)) = 0 := if_neg hji
      have hif :
          (if j = i then 𝟙 (SheafOfModules.unit Y.ringCatSheaf) else
            (0 : SheafOfModules.unit Y.ringCatSheaf ⟶
              SheafOfModules.unit Y.ringCatSheaf)) = 0 := if_neg hji
      have hifF := congrArg
        (fun q : SheafOfModules.unit Y.ringCatSheaf ⟶
            SheafOfModules.unit Y.ringCatSheaf => η.hom ≫ F.map q ≫ η.inv) hif
      have hmid : (0 : SheafOfModules.unit X.ringCatSheaf ⟶
          SheafOfModules.unit X.ringCatSheaf) = η.hom ≫ F.map
            (if j = i then 𝟙 (SheafOfModules.unit Y.ringCatSheaf) else
              (0 : SheafOfModules.unit Y.ringCatSheaf ⟶
                SheafOfModules.unit Y.ringCatSheaf)) ≫ η.inv :=
        (restriction_iso_hom_map_zero_inv F η).trans hifF.symm
      exact ((hdeltaX.trans hleft).trans hmid).trans hdeltaYF.symm
  have htrans := congrArg
    (fun q => (q ≫ F.map (freeCoordinateMap (X := Y) I i)) ≫ η.inv) hmap
  have hfirst :
      SheafOfModules.ιFree (R := X.ringCatSheaf) j ≫ e.hom ≫ e.inv ≫
        freeCoordinateMap (X := X) I i =
      SheafOfModules.ιFree (R := X.ringCatSheaf) j ≫
        freeCoordinateMap (X := X) I i := by simp
  have hlast :
      ((SheafOfModules.ιFree (R := X.ringCatSheaf) j ≫ e.hom) ≫
          F.map (freeCoordinateMap (X := Y) I i)) ≫ η.inv =
        SheafOfModules.ιFree (R := X.ringCatSheaf) j ≫ e.hom ≫
          F.map (freeCoordinateMap (X := Y) I i) ≫
          (AlgebraicGeometry.Scheme.Modules.restrictUnitIso f).hom := by
    have hη : η.inv = (AlgebraicGeometry.Scheme.Modules.restrictUnitIso f).hom := rfl
    have hη' := congrArg
      (fun q => ((SheafOfModules.ιFree (R := X.ringCatSheaf) j ≫ e.hom) ≫
        F.map (freeCoordinateMap (X := Y) I i)) ≫ q) hη
    exact hη'.trans
      ((Category.assoc _ _ _).trans (Category.assoc _ _ _))
  exact (((hfirst.trans hdelta).trans hcomp.symm).trans htrans.symm).trans hlast


noncomputable def restrictFreeSection {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (I : Type u)
    (s : (SheafOfModules.free (R := Y.ringCatSheaf) I).sections) :
    (SheafOfModules.free (R := X.ringCatSheaf) I).sections :=
  (SheafOfModules.free (R := X.ringCatSheaf) I).unitHomEquiv
    ((AlgebraicGeometry.Scheme.Modules.restrictUnitIso f).symm.hom ≫
      (AlgebraicGeometry.Scheme.Modules.restrictFunctor f).map
        ((SheafOfModules.free (R := Y.ringCatSheaf) I).unitHomEquiv.symm s) ≫
      (restrictionFreeIso f I).inv)

theorem restrictFreeSection_coordinate_hom {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (I : Type u)
    [DecidableEq I] (s : (SheafOfModules.free (R := Y.ringCatSheaf) I).sections)
    (i : I) :
    (SheafOfModules.free (R := X.ringCatSheaf) I).unitHomEquiv.symm
        (restrictFreeSection f I s) ≫ freeCoordinateMap (X := X) I i =
      (AlgebraicGeometry.Scheme.Modules.restrictUnitIso f).inv ≫
        (AlgebraicGeometry.Scheme.Modules.restrictFunctor f).map
          ((SheafOfModules.free (R := Y.ringCatSheaf) I).unitHomEquiv.symm s ≫
            freeCoordinateMap (X := Y) I i) ≫
        (AlgebraicGeometry.Scheme.Modules.restrictUnitIso f).hom := by
  unfold restrictFreeSection
  rw [Equiv.symm_apply_apply]
  let F := AlgebraicGeometry.Scheme.Modules.restrictFunctor f
  let η := (AlgebraicGeometry.Scheme.Modules.restrictUnitIso f).symm
  let a := η.hom
  let b := F.map ((SheafOfModules.free (R := Y.ringCatSheaf) I).unitHomEquiv.symm s)
  let c := (restrictionFreeIso f I).inv
  let d := freeCoordinateMap (X := X) I i
  let q := F.map (freeCoordinateMap (X := Y) I i)
  let z := (AlgebraicGeometry.Scheme.Modules.restrictUnitIso f).hom
  change ((a ≫ b) ≫ c) ≫ d = η.hom ≫ F.map
    ((SheafOfModules.free (R := Y.ringCatSheaf) I).unitHomEquiv.symm s ≫
      freeCoordinateMap (X := Y) I i) ≫ z
  have hcd : c ≫ d = q ≫ z := by
    exact restrictionFreeIso_inv_comp_freeCoordinateMap f I i
  have hcd' := congrArg (fun w => (a ≫ b) ≫ w) hcd
  have hbc : b ≫ q = F.map
      ((SheafOfModules.free (R := Y.ringCatSheaf) I).unitHomEquiv.symm s ≫
        freeCoordinateMap (X := Y) I i) := by
    exact (F.map_comp _ _).symm
  have hbc' := congrArg (fun w => a ≫ (w ≫ z)) hbc
  exact (Category.assoc _ _ _).trans
    (hcd'.trans ((Category.assoc _ _ _).trans
      ((congrArg (fun w => a ≫ w) (Category.assoc _ _ _).symm).trans hbc')))

theorem restrictionFreeIsoOf_inv_sections_eq_restrictFreeSection {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {E : Y.Modules} (I : Type u) [DecidableEq I]
    (e : SheafOfModules.free (R := Y.ringCatSheaf) I ≅ E) (s : E.sections) :
    SheafOfModules.sectionsMap (restrictionFreeIsoOf f I e).inv
      (restrictModuleSection f E s) =
      restrictFreeSection f I (SheafOfModules.sectionsMap e.inv s) := by
  apply (SheafOfModules.free (R := X.ringCatSheaf) I).unitHomEquiv.symm.injective
  have hleft :
      (SheafOfModules.free (R := X.ringCatSheaf) I).unitHomEquiv.symm
        (SheafOfModules.sectionsMap (restrictionFreeIsoOf f I e).inv
          (restrictModuleSection f E s)) =
      ((AlgebraicGeometry.Scheme.Modules.restrictFunctor f).obj E).unitHomEquiv.symm
        (restrictModuleSection f E s) ≫ (restrictionFreeIsoOf f I e).inv :=
    (SheafOfModules.unitHomEquiv_symm_comp
      (restrictModuleSection f E s) (restrictionFreeIsoOf f I e).inv).symm
  have hright :
      (SheafOfModules.free (R := X.ringCatSheaf) I).unitHomEquiv.symm
        (restrictFreeSection f I (SheafOfModules.sectionsMap e.inv s)) =
      (AlgebraicGeometry.Scheme.Modules.restrictUnitIso f).symm.hom ≫
        (AlgebraicGeometry.Scheme.Modules.restrictFunctor f).map
          (E.unitHomEquiv.symm s ≫ e.inv) ≫ (restrictionFreeIso f I).inv := by
    unfold restrictFreeSection
    rw [Equiv.symm_apply_apply]
    exact congrArg (fun q =>
      (AlgebraicGeometry.Scheme.Modules.restrictUnitIso f).symm.hom ≫
        (AlgebraicGeometry.Scheme.Modules.restrictFunctor f).map q ≫
        (restrictionFreeIso f I).inv)
      (SheafOfModules.unitHomEquiv_symm_comp s e.inv).symm
  have hmiddle :
      ((AlgebraicGeometry.Scheme.Modules.restrictFunctor f).obj E).unitHomEquiv.symm
        (restrictModuleSection f E s) ≫ (restrictionFreeIsoOf f I e).inv =
      (AlgebraicGeometry.Scheme.Modules.restrictUnitIso f).symm.hom ≫
        (AlgebraicGeometry.Scheme.Modules.restrictFunctor f).map
          (E.unitHomEquiv.symm s ≫ e.inv) ≫ (restrictionFreeIso f I).inv := by
    unfold restrictModuleSection restrictionFreeIsoOf
    rw [Equiv.symm_apply_apply]
    let F := AlgebraicGeometry.Scheme.Modules.restrictFunctor f
    let η := (AlgebraicGeometry.Scheme.Modules.restrictUnitIso f).symm
    let a := η.hom
    let b := F.map (E.unitHomEquiv.symm s)
    let c := F.map e.inv
    let d := (restrictionFreeIso f I).inv
    change (a ≫ b) ≫ (c ≫ d) = a ≫ F.map
      (E.unitHomEquiv.symm s ≫ e.inv) ≫ d
    have hbc : b ≫ c = F.map (E.unitHomEquiv.symm s ≫ e.inv) := by
      exact (F.map_comp _ _).symm
    have hbc' := congrArg (fun q => a ≫ q ≫ d) hbc
    exact (Category.assoc _ _ _).trans hbc'
  exact hleft.trans (hmiddle.trans hright.symm)

/-- A free-section coordinate restricts correctly once the corresponding
coordinate morphism is identified with the canonical restricted scalar
endomorphism.  The remaining free-module calculation is therefore separated
from the calculation on the structure sheaf proved above. -/
theorem freeSectionCoordinate_restrict_eq_appTop_of_hom
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (I : Type u) (s : (SheafOfModules.free (R := Y.ringCatSheaf) I).sections)
    (t : (SheafOfModules.free (R := X.ringCatSheaf) I).sections) (i : I)
    (h : (SheafOfModules.free (R := X.ringCatSheaf) I).unitHomEquiv.symm t ≫
        freeCoordinateMap (X := X) I i =
      (AlgebraicGeometry.Scheme.Modules.restrictUnitIso f).inv ≫
        (AlgebraicGeometry.Scheme.Modules.restrictFunctor f).map
          ((SheafOfModules.free (R := Y.ringCatSheaf) I).unitHomEquiv.symm s ≫
            freeCoordinateMap (X := Y) I i) ≫
        (AlgebraicGeometry.Scheme.Modules.restrictUnitIso f).hom) :
    freeSectionCoordinate (X := X) I t i =
      f.appTop (freeSectionCoordinate (X := Y) I s i) := by
  unfold freeSectionCoordinate
  change unitEndomorphismValue (X := X)
    ((SheafOfModules.free (R := X.ringCatSheaf) I).unitHomEquiv.symm t ≫
      freeCoordinateMap (X := X) I i) = _
  rw [h]
  exact unitEndomorphismValue_restrict_eq_appTop f _

theorem freeSectionCoordinate_restrictFreeSection_eq_appTop {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (I : Type u)
    [DecidableEq I] (s : (SheafOfModules.free (R := Y.ringCatSheaf) I).sections)
    (i : I) :
    freeSectionCoordinate (X := X) I (restrictFreeSection f I s) i =
      f.appTop (freeSectionCoordinate (X := Y) I s i) := by
  apply freeSectionCoordinate_restrict_eq_appTop_of_hom f I s
    (restrictFreeSection f I s) i
  exact restrictFreeSection_coordinate_hom f I s i

/-- Pulling the ideal sheaf induced by a global ideal across an open immersion
of affine schemes is the ideal sheaf induced by extension of that ideal along
the restriction map on global functions. -/
theorem idealSheafData_comap_ofIdealTop_of_isOpenImmersion
    {X Y : Scheme.{u}} [AlgebraicGeometry.IsAffine X] [AlgebraicGeometry.IsAffine Y]
    (f : X ⟶ Y) [IsOpenImmersion f] (I : Ideal Γ(Y, ⊤)) :
    AlgebraicGeometry.Scheme.IdealSheafData.comap
      (AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop I) f =
      AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop (X := X)
        (I.map f.appTop.hom) := by
  apply AlgebraicGeometry.Scheme.IdealSheafData.ext_of_isAffine
  rw [AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  simp only [AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop_ideal]
  let e := (f.appIso ⊤).commRingCatIsoToRingEquiv
  let r : Γ(Y, ⊤) →+* Γ(Y, f ''ᵁ ⊤) :=
    (Y.presheaf.map (homOfLE le_top).op).hom
  let q : Γ(X, ⊤) →+* Γ(X, ⊤) :=
    (X.presheaf.map (homOfLE le_top).op).hom
  have he : e.toRingHom.comp r = f.appTop.hom := by
    exact appIsoTop_comp_restrict_eq_appTop f
  have hq : q = RingHom.id _ := by
    dsimp [q]
    ext x
    simp
  change Ideal.comap e.symm (Ideal.map r I) = Ideal.map q (Ideal.map f.appTop.hom I)
  rw [Ideal.comap_symm e]
  change Ideal.map e.toRingHom (Ideal.map r I) = _
  rw [Ideal.map_map]
  rw [he, hq]
  simp


/-- If the coordinates of a free section on an affine open are the restrictions
of the coordinates on a larger affine chart, then its coordinate zero ideal is
the pullback of the larger chart's zero ideal. -/
theorem freeSectionZeroIdeal_comap_eq_of_coordinate_restrict
    {X Y : Scheme.{u}} [AlgebraicGeometry.IsAffine X] [AlgebraicGeometry.IsAffine Y]
    (f : X ⟶ Y) [IsOpenImmersion f] (I : Type u)
    (s : (SheafOfModules.free (R := Y.ringCatSheaf) I).sections)
    (t : (SheafOfModules.free (R := X.ringCatSheaf) I).sections)
    (h : ∀ i, freeSectionCoordinate (X := X) I t i =
      f.appTop (freeSectionCoordinate (X := Y) I s i)) :
    AlgebraicGeometry.Scheme.IdealSheafData.comap
      (freeSectionZeroIdeal (X := Y) I s) f =
      freeSectionZeroIdeal (X := X) I t := by
  unfold freeSectionZeroIdeal
  rw [idealSheafData_comap_ofIdealTop_of_isOpenImmersion]
  congr 1
  rw [Ideal.map_span]
  apply congrArg Ideal.span
  ext x
  constructor
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, h i⟩
  · rintro ⟨i, rfl⟩
    exact ⟨freeSectionCoordinate (X := Y) I s i, ⟨i, rfl⟩, (h i).symm⟩

/-- On affine schemes, the coordinate zero ideal of a free section pulls back
along an open immersion to the zero ideal of its canonical restriction. -/
theorem freeSectionZeroIdeal_comap_eq_restrictFreeSection
    {X Y : Scheme.{u}} [AlgebraicGeometry.IsAffine X]
    [AlgebraicGeometry.IsAffine Y] (f : X ⟶ Y) [IsOpenImmersion f] (I : Type u)
    [DecidableEq I] (s : (SheafOfModules.free (R := Y.ringCatSheaf) I).sections) :
    AlgebraicGeometry.Scheme.IdealSheafData.comap
      (freeSectionZeroIdeal (X := Y) I s) f =
      freeSectionZeroIdeal (X := X) I (restrictFreeSection f I s) := by
  apply freeSectionZeroIdeal_comap_eq_of_coordinate_restrict f I s
    (restrictFreeSection f I s)
  intro i
  exact freeSectionCoordinate_restrictFreeSection_eq_appTop f I s i

/-- Transporting a presentation and its section along an isomorphism does not
change the associated coordinate zero ideal. -/
theorem sectionZeroIdealOfFreeIso_postcompose_eq {X : Scheme.{u}} {E F : X.Modules}
    (I : Type u) (e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ E) (g : E ≅ F)
    (s : E.sections) :
    sectionZeroIdealOfFreeIso (X := X) I e s =
      sectionZeroIdealOfFreeIso (X := X) I (e ≪≫ g)
        (SheafOfModules.sectionsMap g.hom s) := by
  unfold sectionZeroIdealOfFreeIso
  congr 1
  apply (SheafOfModules.free (R := X.ringCatSheaf) I).unitHomEquiv.symm.injective
  have hleft :
      (SheafOfModules.free (R := X.ringCatSheaf) I).unitHomEquiv.symm
        (SheafOfModules.sectionsMap e.inv s) =
      E.unitHomEquiv.symm s ≫ e.inv :=
    (SheafOfModules.unitHomEquiv_symm_comp s e.inv).symm
  have hright :
      (SheafOfModules.free (R := X.ringCatSheaf) I).unitHomEquiv.symm
        (SheafOfModules.sectionsMap (e ≪≫ g).inv
          (SheafOfModules.sectionsMap g.hom s)) =
      (E.unitHomEquiv.symm s ≫ g.hom) ≫ (g.inv ≫ e.inv) := by
    have h₁ :
        F.unitHomEquiv.symm (SheafOfModules.sectionsMap g.hom s) =
        E.unitHomEquiv.symm s ≫ g.hom :=
      (SheafOfModules.unitHomEquiv_symm_comp s g.hom).symm
    have h₂ :
        (SheafOfModules.free (R := X.ringCatSheaf) I).unitHomEquiv.symm
          (SheafOfModules.sectionsMap (g.inv ≫ e.inv)
            (SheafOfModules.sectionsMap g.hom s)) =
        F.unitHomEquiv.symm (SheafOfModules.sectionsMap g.hom s) ≫
          (g.inv ≫ e.inv) :=
      (SheafOfModules.unitHomEquiv_symm_comp _ _).symm
    exact h₂.trans (congrArg (fun q => q ≫ (g.inv ≫ e.inv)) h₁)
  have hmiddle :
      (E.unitHomEquiv.symm s ≫ g.hom) ≫ (g.inv ≫ e.inv) =
      E.unitHomEquiv.symm s ≫ e.inv := by
    calc
      (E.unitHomEquiv.symm s ≫ g.hom) ≫ (g.inv ≫ e.inv) =
          E.unitHomEquiv.symm s ≫ (g.hom ≫ (g.inv ≫ e.inv)) := Category.assoc _ _ _
      _ = E.unitHomEquiv.symm s ≫ ((g.hom ≫ g.inv) ≫ e.inv) := by
        exact congrArg (fun q => E.unitHomEquiv.symm s ≫ q)
          (Category.assoc _ _ _).symm
      _ = E.unitHomEquiv.symm s ≫ e.inv := by
        have hgi := congrArg
          (fun q => E.unitHomEquiv.symm s ≫ (q ≫ e.inv)) g.hom_inv_id
        exact hgi.trans (congrArg (fun q => E.unitHomEquiv.symm s ≫ q)
          (Category.id_comp e.inv))
  exact hleft.trans (hright.trans hmiddle).symm

/-- The module on the smaller open chart is canonically identified with the
restriction of the module on the larger chart. -/
noncomputable def localRestrictionTargetIso {X : Scheme.{u}} {U V : X.Opens}
    (f : V ⟶ U) {E : X.Modules} :
    (AlgebraicGeometry.Scheme.Modules.overEquiv V).functor.obj (E.over V) ≅
      (AlgebraicGeometry.Scheme.Modules.restrictFunctor
        (X.homOfLE (leOfHom f))).obj
        ((AlgebraicGeometry.Scheme.Modules.overEquiv U).functor.obj (E.over U)) :=
  (AlgebraicGeometry.Scheme.Modules.overEquiv V).functor.mapIso
    ((SheafOfModules.overFunctorMap X.ringCatSheaf f).app E).symm ≪≫
  (AlgebraicGeometry.Scheme.Modules.overMapCompOverEquiv f).app (E.over U)

/-- The comparison identifying two successive over-site restrictions acts
strictly as the identity after passage to modules on the smaller open. -/
theorem overEquiv_map_overFunctorMap_eq_id
    {X : Scheme.{u}} {U V : X.Opens} (f : V ⟶ U) (E : X.Modules) :
    (AlgebraicGeometry.Scheme.Modules.overEquiv V).functor.map
      ((SheafOfModules.overFunctorMap X.ringCatSheaf f).hom.app E) = 𝟙 _ := by
  ext W x
  change (((AlgebraicGeometry.Scheme.Modules.overEquiv V).functor.map
      ((SheafOfModules.overFunctorMap X.ringCatSheaf f).hom.app E)).val.app
        (Opposite.op W)).hom x = x
  rfl

/-- Inverting the canonical chart comparison leaves only the comparison
between restriction and the over-site equivalence: its other factor is
strictly the identity by `overEquiv_map_overFunctorMap_eq_id`. -/
theorem localRestrictionTargetIso_inv_eq_overMapCompOverEquiv_inv
    {X : Scheme.{u}} {E : X.Modules} {U V : X.Opens} (f : V ⟶ U) :
    (localRestrictionTargetIso (E := E) f).inv =
      (AlgebraicGeometry.Scheme.Modules.overMapCompOverEquiv f).inv.app (E.over U) := by
  have hα :
      (AlgebraicGeometry.Scheme.Modules.overEquiv V).functor.map
        ((SheafOfModules.overFunctorMap X.ringCatSheaf f).hom.app E) = 𝟙 _ :=
    overEquiv_map_overFunctorMap_eq_id (X := X) (U := U) (V := V) f E
  unfold localRestrictionTargetIso
  rw [Iso.trans_inv]
  change (AlgebraicGeometry.Scheme.Modules.overMapCompOverEquiv f).inv.app (E.over U) ≫
      (AlgebraicGeometry.Scheme.Modules.overEquiv V).functor.map
        ((SheafOfModules.overFunctorMap X.ringCatSheaf f).hom.app E) = _
  rw [hα]
  exact Category.comp_id _

/-- Naturality of the canonical identification of modules on nested open
charts reduces section restriction to its value on the structure sheaf. -/
theorem localRestrictionTargetIso_inv_naturality_factor
    {X : Scheme.{u}} {E : X.Modules} {U V : X.Opens} (f : V ⟶ U)
    (z : SheafOfModules.unit X.ringCatSheaf ⟶ E) :
    let h := X.homOfLE (leOfHom f)
    let F := AlgebraicGeometry.Scheme.Modules.restrictFunctor h
    let EU := AlgebraicGeometry.Scheme.Modules.overEquiv U
    let EV := AlgebraicGeometry.Scheme.Modules.overEquiv V
    let α := SheafOfModules.overFunctorMap X.ringCatSheaf f
    let β := AlgebraicGeometry.Scheme.Modules.overMapCompOverEquiv f
    (AlgebraicGeometry.Scheme.Modules.restrictUnitIso h).symm.hom ≫
      F.map (EU.functor.map (z.over U)) ≫ β.inv.app (E.over U) ≫
      EV.functor.map (α.hom.app E) =
    ((AlgebraicGeometry.Scheme.Modules.restrictUnitIso h).symm.hom ≫
      β.inv.app ((SheafOfModules.unit X.ringCatSheaf).over U) ≫
      EV.functor.map (α.hom.app (SheafOfModules.unit X.ringCatSheaf))) ≫
      EV.functor.map (z.over V) := by
  dsimp
  let h := X.homOfLE (leOfHom f)
  let F := AlgebraicGeometry.Scheme.Modules.restrictFunctor h
  let EU := AlgebraicGeometry.Scheme.Modules.overEquiv U
  let EV := AlgebraicGeometry.Scheme.Modules.overEquiv V
  let α := SheafOfModules.overFunctorMap X.ringCatSheaf f
  let β := AlgebraicGeometry.Scheme.Modules.overMapCompOverEquiv f
  have hβ := β.inv.naturality (z.over U)
  have hα := α.hom.naturality z
  change F.map (EU.functor.map (z.over U)) ≫ β.inv.app (E.over U) =
    β.inv.app ((SheafOfModules.unit X.ringCatSheaf).over U) ≫
      EV.functor.map ((SheafOfModules.overMap X.ringCatSheaf f).map (z.over U)) at hβ
  change (SheafOfModules.overMap X.ringCatSheaf f).map (z.over U) ≫ α.hom.app E =
    α.hom.app (SheafOfModules.unit X.ringCatSheaf) ≫ z.over V at hα
  calc
    (AlgebraicGeometry.Scheme.Modules.restrictUnitIso h).symm.hom ≫
        F.map (EU.functor.map (z.over U)) ≫ β.inv.app (E.over U) ≫
          EV.functor.map (α.hom.app E) =
      (AlgebraicGeometry.Scheme.Modules.restrictUnitIso h).symm.hom ≫
        (F.map (EU.functor.map (z.over U)) ≫ β.inv.app (E.over U)) ≫
          EV.functor.map (α.hom.app E) := by simp only [Category.assoc]
    _ = (AlgebraicGeometry.Scheme.Modules.restrictUnitIso h).symm.hom ≫
        (β.inv.app ((SheafOfModules.unit X.ringCatSheaf).over U) ≫
          EV.functor.map ((SheafOfModules.overMap X.ringCatSheaf f).map (z.over U))) ≫
          EV.functor.map (α.hom.app E) := by
      exact congrArg (fun q =>
        (AlgebraicGeometry.Scheme.Modules.restrictUnitIso h).symm.hom ≫ q ≫
          EV.functor.map (α.hom.app E)) hβ
    _ = (AlgebraicGeometry.Scheme.Modules.restrictUnitIso h).symm.hom ≫
        β.inv.app ((SheafOfModules.unit X.ringCatSheaf).over U) ≫
        (EV.functor.map ((SheafOfModules.overMap X.ringCatSheaf f).map (z.over U)) ≫
          EV.functor.map (α.hom.app E)) := by rfl
    _ = (AlgebraicGeometry.Scheme.Modules.restrictUnitIso h).symm.hom ≫
        β.inv.app ((SheafOfModules.unit X.ringCatSheaf).over U) ≫
        EV.functor.map ((SheafOfModules.overMap X.ringCatSheaf f).map (z.over U) ≫
          α.hom.app E) := by
      exact congrArg (fun q =>
        (AlgebraicGeometry.Scheme.Modules.restrictUnitIso h).symm.hom ≫
          β.inv.app ((SheafOfModules.unit X.ringCatSheaf).over U) ≫ q)
        (EV.functor.map_comp _ _).symm
    _ = (AlgebraicGeometry.Scheme.Modules.restrictUnitIso h).symm.hom ≫
        β.inv.app ((SheafOfModules.unit X.ringCatSheaf).over U) ≫
        EV.functor.map (α.hom.app (SheafOfModules.unit X.ringCatSheaf) ≫ z.over V) := by
      exact congrArg (fun q =>
        (AlgebraicGeometry.Scheme.Modules.restrictUnitIso h).symm.hom ≫
          β.inv.app ((SheafOfModules.unit X.ringCatSheaf).over U) ≫ EV.functor.map q) hα
    _ = (AlgebraicGeometry.Scheme.Modules.restrictUnitIso h).symm.hom ≫
        β.inv.app ((SheafOfModules.unit X.ringCatSheaf).over U) ≫
        (EV.functor.map (α.hom.app (SheafOfModules.unit X.ringCatSheaf)) ≫
          EV.functor.map (z.over V)) := by
      exact congrArg (fun q =>
        (AlgebraicGeometry.Scheme.Modules.restrictUnitIso h).symm.hom ≫
          β.inv.app ((SheafOfModules.unit X.ringCatSheaf).over U) ≫ q)
        (EV.functor.map_comp _ _)
    _ = ((AlgebraicGeometry.Scheme.Modules.restrictUnitIso h).symm.hom ≫
        β.inv.app ((SheafOfModules.unit X.ringCatSheaf).over U) ≫
        EV.functor.map (α.hom.app (SheafOfModules.unit X.ringCatSheaf))) ≫
          EV.functor.map (z.over V) := by rfl

/-- The unit-object coherence for the canonical restriction identification.
All section coherences follow from this single equality. -/
def localRestrictionUnitCompatible {X : Scheme.{u}} {U V : X.Opens}
    (f : V ⟶ U) : Prop :=
  (AlgebraicGeometry.Scheme.Modules.restrictUnitIso
    (X.homOfLE (leOfHom f))).symm.hom ≫
    (AlgebraicGeometry.Scheme.Modules.overMapCompOverEquiv f).inv.app
      ((SheafOfModules.unit X.ringCatSheaf).over U) ≫
    (AlgebraicGeometry.Scheme.Modules.overEquiv V).functor.map
      ((SheafOfModules.overFunctorMap X.ringCatSheaf f).hom.app
        (SheafOfModules.unit X.ringCatSheaf)) = 𝟙 _

/-- The unit coherence can be checked before the strictly identity
over-site comparison is appended. -/
theorem localRestrictionUnitCompatible_iff
    {X : Scheme.{u}} {U V : X.Opens} (f : V ⟶ U) :
    localRestrictionUnitCompatible f ↔
      (AlgebraicGeometry.Scheme.Modules.restrictUnitIso
        (X.homOfLE (leOfHom f))).symm.hom ≫
        (AlgebraicGeometry.Scheme.Modules.overMapCompOverEquiv f).inv.app
          ((SheafOfModules.unit X.ringCatSheaf).over U) = 𝟙 _ := by
  unfold localRestrictionUnitCompatible
  have hα :
      (AlgebraicGeometry.Scheme.Modules.overEquiv V).functor.map
        ((SheafOfModules.overFunctorMap X.ringCatSheaf f).hom.app
          (SheafOfModules.unit X.ringCatSheaf)) = 𝟙 _ :=
    overEquiv_map_overFunctorMap_eq_id (X := X) (U := U) (V := V) f
      (SheafOfModules.unit X.ringCatSheaf)
  rw [hα]
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-- The inverse of the canonical unit restriction is evaluationwise the
inverse of the ordinary open-immersion section isomorphism. -/
theorem restrictUnitIso_symm_hom_app_apply
    {X : Scheme.{u}} {U V : X.Opens} (f : V ⟶ U)
    (W : (V : Scheme.{u}).Opens)
    (x : Γ(SheafOfModules.unit (V : Scheme.{u}).ringCatSheaf, W)) :
    ((AlgebraicGeometry.Scheme.Modules.restrictUnitIso
      (X.homOfLE (leOfHom f))).symm.hom.val.app (Opposite.op W)) x =
      ((X.homOfLE (leOfHom f)).appIso W).inv x := rfl

/-- The reduced unit comparison is equivalently the pointwise statement
that the over-site comparison inverts the usual restriction isomorphism on
every open of the smaller chart.  This separates its remaining coherence
calculation from all module-section and zero-locus arguments. -/
theorem localRestrictionUnitCore_iff_pointwise
    {X : Scheme.{u}} {U V : X.Opens} (f : V ⟶ U) :
    ((AlgebraicGeometry.Scheme.Modules.restrictUnitIso
      (X.homOfLE (leOfHom f))).symm.hom ≫
      (AlgebraicGeometry.Scheme.Modules.overMapCompOverEquiv f).inv.app
        ((SheafOfModules.unit X.ringCatSheaf).over U) = 𝟙 _) ↔
    ∀ (W : (V : Scheme.{u}).Opens)
      (x : Γ(SheafOfModules.unit (V : Scheme.{u}).ringCatSheaf, W)),
      ((AlgebraicGeometry.Scheme.Modules.overMapCompOverEquiv f).inv.app
        ((SheafOfModules.unit X.ringCatSheaf).over U)).val.app (Opposite.op W)
        (((X.homOfLE (leOfHom f)).appIso W).inv x) = x := by
  constructor
  · intro h W x
    have h' := congrArg (fun q => q.val.app (Opposite.op W) x) h
    change ((AlgebraicGeometry.Scheme.Modules.overMapCompOverEquiv f).inv.app
      ((SheafOfModules.unit X.ringCatSheaf).over U)).val.app (Opposite.op W)
      (((AlgebraicGeometry.Scheme.Modules.restrictUnitIso
        (X.homOfLE (leOfHom f))).symm.hom.val.app (Opposite.op W)) x) = x at h'
    rw [restrictUnitIso_symm_hom_app_apply f] at h'
    exact h'
  · intro h
    ext W x
    change (((((AlgebraicGeometry.Scheme.Modules.restrictUnitIso
      (X.homOfLE (leOfHom f))).symm.hom ≫
      (AlgebraicGeometry.Scheme.Modules.overMapCompOverEquiv f).inv.app
        ((SheafOfModules.unit X.ringCatSheaf).over U))).val.app
          (Opposite.op W)).hom) x = x
    change ((AlgebraicGeometry.Scheme.Modules.overMapCompOverEquiv f).inv.app
      ((SheafOfModules.unit X.ringCatSheaf).over U)).val.app (Opposite.op W)
      (((AlgebraicGeometry.Scheme.Modules.restrictUnitIso
        (X.homOfLE (leOfHom f))).symm.hom.val.app (Opposite.op W)) x) = x
    rw [restrictUnitIso_symm_hom_app_apply f]
    exact h W x

/-- On the unit sheaf, the forward over-site comparison is exactly ordinary
restriction of functions to the smaller chart. -/
theorem overMapCompOverEquiv_hom_unit_app_apply
    {X : Scheme.{u}} {U V : X.Opens} (f : V ⟶ U)
    (W : (V : Scheme.{u}).Opens)
    (x : Γ(SheafOfModules.unit (V : Scheme.{u}).ringCatSheaf, W)) :
    ((AlgebraicGeometry.Scheme.Modules.overMapCompOverEquiv f).hom.app
      ((SheafOfModules.unit X.ringCatSheaf).over U)).val.app (Opposite.op W) x =
      ((X.homOfLE (leOfHom f)).appIso W).inv x := by
  rw [AlgebraicGeometry.Scheme.Hom.appIso_homOfLE_inv]
  rfl

/-- The canonical comparison between successive restrictions is coherent on
the structure sheaf.  This discharges the only chart-level condition used by
the zero-locus and Serre-pencil constructions. -/
theorem localRestrictionUnitCore
    {X : Scheme.{u}} {U V : X.Opens} (f : V ⟶ U) :
    (AlgebraicGeometry.Scheme.Modules.restrictUnitIso
      (X.homOfLE (leOfHom f))).symm.hom ≫
      (AlgebraicGeometry.Scheme.Modules.overMapCompOverEquiv f).inv.app
        ((SheafOfModules.unit X.ringCatSheaf).over U) = 𝟙 _ := by
  apply (localRestrictionUnitCore_iff_pointwise f).mpr
  intro W x
  rw [← overMapCompOverEquiv_hom_unit_app_apply f W x]
  have h := congrArg (fun q => q.val.app (Opposite.op W) x)
    ((AlgebraicGeometry.Scheme.Modules.overMapCompOverEquiv f).hom_inv_id_app
      ((SheafOfModules.unit X.ringCatSheaf).over U))
  exact h

/-- A form of `localRestrictionUnitCore` whose unit object is written on the
over-site.  Keeping this as a separate opaque theorem prevents expensive
definitional unfolding in the free-module coherence proof below. -/
theorem localRestrictionUnitCore_overUnit
    {X : Scheme.{u}} {U W : X.Opens} (hWU : W ≤ U) :
    (Scheme.Modules.restrictUnitIso
      (X.homOfLE hWU)).symm.hom ≫
      (Scheme.Modules.overMapCompOverEquiv
        (homOfLE hWU)).inv.app
          (SheafOfModules.unit (X.ringCatSheaf.over U)) = 𝟙 _ := by
  exact localRestrictionUnitCore
    (X := X) (U := U) (V := W) (homOfLE hWU)

/-- Restricting a morphism out of the unit object through the over-site
comparison is the same as first applying the over-site restriction functor. -/
theorem overMapSectionCore
    {X : Scheme.{u}} {U W : X.Opens} (hWU : W ≤ U)
    {A : SheafOfModules (X.ringCatSheaf.over U)}
    (z : SheafOfModules.unit (X.ringCatSheaf.over U) ⟶ A) :
    (Scheme.Modules.restrictUnitIso (X.homOfLE hWU)).symm.hom ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map
          ((Scheme.Modules.overEquiv U).functor.map z) ≫
        (Scheme.Modules.overMapCompOverEquiv
          (homOfLE hWU)).inv.app A =
      (Scheme.Modules.overEquiv W).functor.map
        ((SheafOfModules.overMap X.ringCatSheaf
          (homOfLE hWU)).map z) := by
  have hβ := (Scheme.Modules.overMapCompOverEquiv
    (homOfLE hWU)).inv.naturality z
  have hunit := localRestrictionUnitCore_overUnit
    (X := X) (U := U) (W := W) hWU
  calc
    (Scheme.Modules.restrictUnitIso (X.homOfLE hWU)).symm.hom ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map
          ((Scheme.Modules.overEquiv U).functor.map z) ≫
        (Scheme.Modules.overMapCompOverEquiv
          (homOfLE hWU)).inv.app A =
      (Scheme.Modules.restrictUnitIso (X.homOfLE hWU)).symm.hom ≫
        ((Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map
            ((Scheme.Modules.overEquiv U).functor.map z) ≫
          (Scheme.Modules.overMapCompOverEquiv
            (homOfLE hWU)).inv.app A) := rfl
    _ = (Scheme.Modules.restrictUnitIso (X.homOfLE hWU)).symm.hom ≫
        ((Scheme.Modules.overMapCompOverEquiv
            (homOfLE hWU)).inv.app
              (SheafOfModules.unit (X.ringCatSheaf.over U)) ≫
          (Scheme.Modules.overEquiv W).functor.map
            ((SheafOfModules.overMap X.ringCatSheaf
              (homOfLE hWU)).map z)) :=
      congrArg (fun q =>
        (Scheme.Modules.restrictUnitIso (X.homOfLE hWU)).symm.hom ≫ q) hβ
    _ = ((Scheme.Modules.restrictUnitIso (X.homOfLE hWU)).symm.hom ≫
          (Scheme.Modules.overMapCompOverEquiv
            (homOfLE hWU)).inv.app
              (SheafOfModules.unit (X.ringCatSheaf.over U))) ≫
        (Scheme.Modules.overEquiv W).functor.map
          ((SheafOfModules.overMap X.ringCatSheaf
            (homOfLE hWU)).map z) := (Category.assoc _ _ _).symm
    _ = _ := by
      rw [hunit]
      exact Category.id_comp _

/-- Reassociated form of `overMapSectionCore` with an arbitrary morphism
postcomposed. -/
theorem overMapSectionCore_assoc
    {X : Scheme.{u}} {U W : X.Opens} (hWU : W ≤ U)
    {A : SheafOfModules (X.ringCatSheaf.over U)}
    (z : SheafOfModules.unit (X.ringCatSheaf.over U) ⟶ A)
    {B : (W : Scheme.{u}).Modules}
    (q : (Scheme.Modules.overEquiv W).functor.obj
        ((SheafOfModules.overMap X.ringCatSheaf
          (homOfLE hWU)).obj A) ⟶ B) :
    (Scheme.Modules.restrictUnitIso (X.homOfLE hWU)).symm.hom ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map
          ((Scheme.Modules.overEquiv U).functor.map z) ≫
        (Scheme.Modules.overMapCompOverEquiv
          (homOfLE hWU)).inv.app A ≫ q =
      (Scheme.Modules.overEquiv W).functor.map
          ((SheafOfModules.overMap X.ringCatSheaf
            (homOfLE hWU)).map z) ≫ q :=
  congrArg (fun f => f ≫ q) (overMapSectionCore hWU z)

/-- Naturality of the inverse comparison between restriction and passage to
an over-site, expressed as an equality of composite isomorphisms. -/
theorem overMapCompOverEquiv_inv_naturality_iso
    {X : Scheme.{u}} {U W : X.Opens} (hWU : W ≤ U)
    {A B : SheafOfModules (X.ringCatSheaf.over U)} (t : A ≅ B) :
    ((Scheme.Modules.overMapCompOverEquiv
        (homOfLE hWU)).app A).symm ≪≫
      (Scheme.Modules.overEquiv W).functor.mapIso
        ((SheafOfModules.overMap X.ringCatSheaf
          (homOfLE hWU)).mapIso t) =
    (Scheme.Modules.restrictFunctor
      (X.homOfLE hWU)).mapIso
        ((Scheme.Modules.overEquiv U).functor.mapIso t) ≪≫
      ((Scheme.Modules.overMapCompOverEquiv
        (homOfLE hWU)).app B).symm := by
  apply Iso.ext
  exact ((Scheme.Modules.overMapCompOverEquiv
    (homOfLE hWU)).inv.naturality t.hom).symm

set_option backward.isDefEq.respectTransparency false in
/-- The canonical free-module comparison on an over-site commutes with
restriction to a smaller open. -/
theorem overEquivFreeIso_restrict
    {X : Scheme.{u}} {U W : X.Opens} (hWU : W ≤ U)
    (I : Type u) :
    overEquivFreeIso (X := X) W I ≪≫
        (Scheme.Modules.overEquiv W).functor.mapIso
          (SheafOfModules.mapFreeIso
            (SheafOfModules.overMap X.ringCatSheaf (homOfLE hWU)) I
            (SheafOfModules.overMapUnitIso (homOfLE hWU)).symm) =
      restrictionFreeIso
          (X.homOfLE hWU) I ≪≫
        (Scheme.Modules.restrictFunctor
          (X.homOfLE hWU)).mapIso
          (overEquivFreeIso (X := X) U I) ≪≫
        ((Scheme.Modules.overMapCompOverEquiv
          (homOfLE hWU)).app
            (SheafOfModules.free (R := X.ringCatSheaf.over U) I)).symm := by
  letI hpresWSize : PreservesColimitsOfSize.{u, u}
      (Scheme.Modules.overEquiv W).functor :=
    (Scheme.Modules.overEquiv W).toAdjunction.leftAdjoint_preservesColimits
  letI hpresW : PreservesColimitsOfShape (Discrete I)
      (Scheme.Modules.overEquiv W).functor :=
    PreservesColimitsOfSize.preservesColimitsOfShape
  letI hpresUSize : PreservesColimitsOfSize.{u, u}
      (Scheme.Modules.overEquiv U).functor :=
    (Scheme.Modules.overEquiv U).toAdjunction.leftAdjoint_preservesColimits
  letI hpresU : PreservesColimitsOfShape (Discrete I)
      (Scheme.Modules.overEquiv U).functor :=
    PreservesColimitsOfSize.preservesColimitsOfShape
  letI hpresF : PreservesColimitsOfShape (Discrete I)
      (Scheme.Modules.restrictFunctor (X.homOfLE hWU)) :=
    (Scheme.Modules.restrictAdjunction
      (X.homOfLE hWU)).leftAdjoint_preservesColimits
        |>.preservesColimitsOfShape
  apply Iso.ext
  apply ((Scheme.Modules.overEquiv W).functor.obj
    ((SheafOfModules.overMap X.ringCatSheaf
      (homOfLE hWU)).obj
        (SheafOfModules.free (R := X.ringCatSheaf.over U) I))).freeHomEquiv.injective
  funext i
  apply ((Scheme.Modules.overEquiv W).functor.obj
    ((SheafOfModules.overMap X.ringCatSheaf
      (homOfLE hWU)).obj
        (SheafOfModules.free (R := X.ringCatSheaf.over U) I))).unitHomEquiv.symm.injective
  rw [SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply,
    SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
  unfold overEquivFreeIso
  unfold restrictionFreeIso
  erw [Iso.trans_hom]
  conv_rhs => erw [Iso.trans_hom]
  conv_rhs => erw [Iso.trans_hom]
  dsimp only
  have hW := @SheafOfModules.ιFree_mapFreeIso_hom_assoc
    _ _ _ _ _ _ _ _ _ _ _ _
    (Scheme.Modules.overEquiv W).functor I hpresW
    (TopologicalSpace.Opens.sheafOfModulesEquivOverUnit
      W X.ringCatSheaf).symm i _
    ((Scheme.Modules.overEquiv W).functor.mapIso
      (SheafOfModules.mapFreeIso
        (SheafOfModules.overMap X.ringCatSheaf (homOfLE hWU)) I
        (SheafOfModules.overMapUnitIso (homOfLE hWU)).symm)).hom
  erw [hW]
  let eUFree := @SheafOfModules.mapFreeIso
    _ _ _ _ _ _ _ _ _ _ _ _
    (Scheme.Modules.overEquiv U).functor I hpresU
    (TopologicalSpace.Opens.sheafOfModulesEquivOverUnit
      U X.ringCatSheaf).symm
  let tail := ((Scheme.Modules.restrictFunctor
      (X.homOfLE hWU)).mapIso eUFree).hom ≫
    ((Scheme.Modules.overMapCompOverEquiv
      (homOfLE hWU)).app
        (SheafOfModules.free (R := X.ringCatSheaf.over U) I)).symm.hom
  have hF := @SheafOfModules.ιFree_mapFreeIso_hom_assoc
    _ _ _ _ _ _ _ _ _ _ _ _
    (Scheme.Modules.restrictFunctor (X.homOfLE hWU)) I hpresF
    (Scheme.Modules.restrictUnitIso (X.homOfLE hWU)).symm i _ tail
  dsimp only [tail, eUFree] at hF
  conv_rhs => erw [hF]
  simp only [Functor.mapIso_hom]
  have hO := @SheafOfModules.ιFree_mapFreeIso_hom
    _ _ _ _ _ _ _ _ _ _ _ _
    (SheafOfModules.overMap X.ringCatSheaf (homOfLE hWU)) I _
    (SheafOfModules.overMapUnitIso (homOfLE hWU)).symm i
  have hU := @SheafOfModules.ιFree_mapFreeIso_hom
    _ _ _ _ _ _ _ _ _ _ _ _
    (Scheme.Modules.overEquiv U).functor I hpresU
    (TopologicalSpace.Opens.sheafOfModulesEquivOverUnit
      U X.ringCatSheaf).symm i
  rw [← (Scheme.Modules.overEquiv W).functor.map_comp, hO,
    (Scheme.Modules.overEquiv W).functor.map_comp]
  have hUmap := congrArg
    (fun q => (Scheme.Modules.restrictFunctor
      (X.homOfLE hWU)).map q) hU
  simp only [Functor.map_comp] at hUmap
  conv_rhs =>
    congr
    · skip
    · erw [← Category.assoc]
      rw [hUmap]
  have hβ := (Scheme.Modules.overMapCompOverEquiv
    (homOfLE hWU)).inv.naturality
      (SheafOfModules.ιFree
        (R := X.ringCatSheaf.over U) i)
  change (Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map
        ((Scheme.Modules.overEquiv U).functor.map
          (SheafOfModules.ιFree i)) ≫
      (Scheme.Modules.overMapCompOverEquiv
        (homOfLE hWU)).inv.app
          (SheafOfModules.free (R := X.ringCatSheaf.over U) I) =
    (Scheme.Modules.overMapCompOverEquiv
        (homOfLE hWU)).inv.app
          (SheafOfModules.unit (X.ringCatSheaf.over U)) ≫
      (Scheme.Modules.overEquiv W).functor.map
        ((SheafOfModules.overMap X.ringCatSheaf
          (homOfLE hWU)).map (SheafOfModules.ιFree i)) at hβ
  simp only [Category.assoc]
  erw [hβ]
  have hleft :
      (TopologicalSpace.Opens.sheafOfModulesEquivOverUnit
          W X.ringCatSheaf).symm.hom ≫
        (Scheme.Modules.overEquiv W).functor.map
          (SheafOfModules.overMapUnitIso
            (homOfLE hWU)).symm.hom = 𝟙 _ := by
    ext V x
    rfl
  have hright := localRestrictionUnitCore_overUnit
    (X := X) (U := U) (W := W) hWU
  erw [← Category.assoc, hleft]
  erw [← Category.assoc, hright]
  rfl

private theorem iso_trans_assoc_five
    {C : Type*} [Category C]
    {A B C₁ D E F : C}
    (a : A ≅ B) (b : B ≅ C₁) (c : C₁ ≅ D)
    (d : D ≅ E) (e : E ≅ F) :
    ((a ≪≫ b ≪≫ c) ≪≫ d ≪≫ e) =
      (a ≪≫ b) ≪≫ ((c ≪≫ d) ≪≫ e) := by
  simp only [Iso.trans_assoc]

/-- A local free frame obtained by canonically restricting a frame on a
larger open agrees with restriction of the corresponding frame on schemes. -/
theorem localFreeIsoOfOver_restrictFreeIsoOver
    {X : Scheme.{u}} {U W : X.Opens} (hWU : W ≤ U)
    (I : Type u)
    (M : X.Modules)
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U) :
    localFreeIsoOfOver W I
        (restrictFreeIsoOver (homOfLE hWU) I t) =
      restrictionFreeIsoOf
          (X.homOfLE hWU) I
          (localFreeIsoOfOver U I t) ≪≫
        (localRestrictionTargetIso
          (E := M) (homOfLE hWU)).symm := by
  unfold localFreeIsoOfOver
  unfold restrictFreeIsoOver
  unfold restrictionFreeIsoOf
  unfold localRestrictionTargetIso
  simp only [Functor.mapIso_trans, Functor.mapIso_symm]
  conv_rhs =>
    erw [Functor.mapIso_trans]
    erw [Iso.trans_symm]
  simp only [Iso.symm_symm_eq]
  conv_lhs => erw [← Iso.trans_assoc]
  have hcore := overEquivFreeIso_restrict hWU I
  rw [hcore]
  have hnat := congrArg
    (fun q => q ≪≫ (Scheme.Modules.overEquiv W).functor.mapIso
      ((SheafOfModules.overFunctorMap X.ringCatSheaf
        (homOfLE hWU)).app M))
    (overMapCompOverEquiv_inv_naturality_iso hWU t)
  simp only [Iso.trans_assoc] at hnat
  let p := restrictionFreeIso
      (X.homOfLE hWU) I ≪≫
    (Scheme.Modules.restrictFunctor
      (X.homOfLE hWU)).mapIso
        (overEquivFreeIso U I)
  have hp := congrArg (fun q => p ≪≫ q) hnat
  dsimp only [p] at hp
  exact (iso_trans_assoc_five
    (restrictionFreeIso (X.homOfLE hWU) I)
    ((Scheme.Modules.restrictFunctor
      (X.homOfLE hWU)).mapIso
        (overEquivFreeIso U I))
    ((Scheme.Modules.overMapCompOverEquiv
      (homOfLE hWU)).app
        (SheafOfModules.free (R := X.ringCatSheaf.over U) I)).symm
    ((Scheme.Modules.overEquiv W).functor.mapIso
      ((SheafOfModules.overMap X.ringCatSheaf
        (homOfLE hWU)).mapIso t))
    ((Scheme.Modules.overEquiv W).functor.mapIso
      ((SheafOfModules.overFunctorMap X.ringCatSheaf
        (homOfLE hWU)).app M))).trans
      (hp.trans (iso_trans_assoc_five
        (restrictionFreeIso (X.homOfLE hWU) I)
        ((Scheme.Modules.restrictFunctor
          (X.homOfLE hWU)).mapIso
            (overEquivFreeIso U I))
        ((Scheme.Modules.restrictFunctor
          (X.homOfLE hWU)).mapIso
            ((Scheme.Modules.overEquiv U).functor.mapIso t))
        ((Scheme.Modules.overMapCompOverEquiv
          (homOfLE hWU)).app (M.over U)).symm
        ((Scheme.Modules.overEquiv W).functor.mapIso
          ((SheafOfModules.overFunctorMap X.ringCatSheaf
            (homOfLE hWU)).app M))).symm)

/-- The full chart-unit coherence follows from the proved core comparison. -/
theorem localRestrictionUnitCompatible_proof
    {X : Scheme.{u}} {U V : X.Opens} (f : V ⟶ U) :
    localRestrictionUnitCompatible f :=
  (localRestrictionUnitCompatible_iff f).mpr (localRestrictionUnitCore f)

/-- The restriction coherence for every module section follows from the
corresponding canonical coherence for the structure sheaf. -/
theorem localRestrictionTargetIso_sectionCompatibility_of_unit
    {X : Scheme.{u}} {E : X.Modules} {U V : X.Opens} (f : V ⟶ U)
    (hunit : localRestrictionUnitCompatible f)
    (s : E.sections) :
    SheafOfModules.sectionsMap
      (localRestrictionTargetIso (E := E) f).inv
      (restrictModuleSection (X.homOfLE (leOfHom f))
        ((AlgebraicGeometry.Scheme.Modules.overEquiv U).functor.obj (E.over U))
        (restrictSectionToOpen (X := X) U s)) =
      restrictSectionToOpen (X := X) V s := by
  let h := X.homOfLE (leOfHom f)
  let F := AlgebraicGeometry.Scheme.Modules.restrictFunctor h
  let EU := AlgebraicGeometry.Scheme.Modules.overEquiv U
  let EV := AlgebraicGeometry.Scheme.Modules.overEquiv V
  let α := SheafOfModules.overFunctorMap X.ringCatSheaf f
  let β := AlgebraicGeometry.Scheme.Modules.overMapCompOverEquiv f
  let z := E.unitHomEquiv.symm s
  apply (EV.functor.obj (E.over V)).unitHomEquiv.symm.injective
  rw [← ((F.obj (EU.functor.obj (E.over U))).unitHomEquiv_symm_comp
    _ (localRestrictionTargetIso (E := E) f).inv)]
  dsimp [restrictModuleSection, restrictSectionToOpen, localRestrictionTargetIso]
  have hEU :
      (EU.functor.obj (E.over U)).unitHomEquiv.symm
        ((EU.functor.obj (E.over U)).unitHomEquiv (EU.functor.map (z.over U))) =
      EU.functor.map (z.over U) :=
    (EU.functor.obj (E.over U)).unitHomEquiv.symm_apply_apply _
  have hF (q : SheafOfModules.unit (V : Scheme.{u}).ringCatSheaf ⟶
      F.obj (EU.functor.obj (E.over U))) :
      (F.obj (EU.functor.obj (E.over U))).unitHomEquiv.symm
        ((F.obj (EU.functor.obj (E.over U))).unitHomEquiv q) = q :=
    (F.obj (EU.functor.obj (E.over U))).unitHomEquiv.symm_apply_apply q
  have hEV :
      (EV.functor.obj (E.over V)).unitHomEquiv.symm
        ((EV.functor.obj (E.over V)).unitHomEquiv (EV.functor.map (z.over V))) =
      EV.functor.map (z.over V) :=
    (EV.functor.obj (E.over V)).unitHomEquiv.symm_apply_apply _
  rw [hEU, hF, hEV]
  change (AlgebraicGeometry.Scheme.Modules.restrictUnitIso h).symm.hom ≫
      F.map (EU.functor.map (z.over U)) ≫
      β.inv.app (E.over U) ≫ EV.functor.map (α.hom.app E) =
    EV.functor.map (z.over V)
  rw [localRestrictionTargetIso_inv_naturality_factor f z]
  change (AlgebraicGeometry.Scheme.Modules.restrictUnitIso h).symm.hom ≫
      β.inv.app ((SheafOfModules.unit X.ringCatSheaf).over U) ≫
      EV.functor.map (α.hom.app (SheafOfModules.unit X.ringCatSheaf)) = 𝟙 _ at hunit
  rw [hunit]
  exact Category.id_comp _

/-- The section restriction formula using the reduced unit coherence from
`localRestrictionUnitCompatible_iff`. -/
theorem localRestrictionTargetIso_sectionCompatibility_of_core
    {X : Scheme.{u}} {E : X.Modules} {U V : X.Opens} (f : V ⟶ U)
    (hcore :
      (AlgebraicGeometry.Scheme.Modules.restrictUnitIso
        (X.homOfLE (leOfHom f))).symm.hom ≫
        (AlgebraicGeometry.Scheme.Modules.overMapCompOverEquiv f).inv.app
          ((SheafOfModules.unit X.ringCatSheaf).over U) = 𝟙 _)
    (s : E.sections) :
    SheafOfModules.sectionsMap
      (localRestrictionTargetIso (E := E) f).inv
      (restrictModuleSection (X.homOfLE (leOfHom f))
        ((AlgebraicGeometry.Scheme.Modules.overEquiv U).functor.obj (E.over U))
        (restrictSectionToOpen (X := X) U s)) =
      restrictSectionToOpen (X := X) V s := by
  exact localRestrictionTargetIso_sectionCompatibility_of_unit f
    ((localRestrictionUnitCompatible_iff f).mpr hcore) s

/-- Canonically restricted sections agree on every pair of nested charts. -/
theorem localRestrictionTargetIso_sectionCompatibility
    {X : Scheme.{u}} {E : X.Modules} {U V : X.Opens} (f : V ⟶ U)
    (s : E.sections) :
    SheafOfModules.sectionsMap
      (localRestrictionTargetIso (E := E) f).inv
      (restrictModuleSection (X.homOfLE (leOfHom f))
        ((AlgebraicGeometry.Scheme.Modules.overEquiv U).functor.obj (E.over U))
        (restrictSectionToOpen (X := X) U s)) =
      restrictSectionToOpen (X := X) V s := by
  exact localRestrictionTargetIso_sectionCompatibility_of_core f
    (localRestrictionUnitCore f) s

/-- The coordinate zero ideal of a section in any finite free presentation
commutes with restriction along an affine open immersion when both the
presentation and section are transported canonically. -/
theorem sectionZeroIdealOfFreeIso_comap_eq_canonicalRestriction
    {X Y : Scheme.{u}} [AlgebraicGeometry.IsAffine X]
    [AlgebraicGeometry.IsAffine Y] (f : X ⟶ Y) [IsOpenImmersion f]
    {E : Y.Modules} (I : Type u) [DecidableEq I]
    (e : SheafOfModules.free (R := Y.ringCatSheaf) I ≅ E) (s : E.sections) :
    AlgebraicGeometry.Scheme.IdealSheafData.comap
      (sectionZeroIdealOfFreeIso (X := Y) I e s) f =
      sectionZeroIdealOfFreeIso (X := X) I (restrictionFreeIsoOf f I e)
        (restrictModuleSection f E s) := by
  unfold sectionZeroIdealOfFreeIso
  have hs := restrictionFreeIsoOf_inv_sections_eq_restrictFreeSection f I e s
  exact (freeSectionZeroIdeal_comap_eq_restrictFreeSection f I
    (SheafOfModules.sectionsMap e.inv s)).trans
      (congrArg (freeSectionZeroIdeal (X := X) I) hs.symm)

/-- Two finite-free chart equations define the same ideal on a common affine
open whenever their restricted sections correspond, through a module
isomorphism, up to an invertible scalar.  This is the descent criterion used
for projectively normalized universal sections. -/
theorem sectionZeroIdealOfFreeIso_comap_eq_comap_of_iso_scale
    {W U V : Scheme.{u}} [AlgebraicGeometry.IsAffine W]
    [AlgebraicGeometry.IsAffine U] [AlgebraicGeometry.IsAffine V]
    (f : W ⟶ U) (g : W ⟶ V) [IsOpenImmersion f] [IsOpenImmersion g]
    {E : U.Modules} {F : V.Modules}
    (I : Type u) [Fintype I] [DecidableEq I]
    (eU : SheafOfModules.free (R := U.ringCatSheaf) I ≅ E)
    (eV : SheafOfModules.free (R := V.ringCatSheaf) I ≅ F)
    (sU : E.sections) (sV : F.sections)
    (α : (AlgebraicGeometry.Scheme.Modules.restrictFunctor f).obj E ≅
      (AlgebraicGeometry.Scheme.Modules.restrictFunctor g).obj F)
    (a : SheafOfModules.unit W.ringCatSheaf ⟶
      SheafOfModules.unit W.ringCatSheaf) [IsIso a]
    (hsection :
      SheafOfModules.sectionsMap α.hom (restrictModuleSection f E sU) =
        scaleSection a (restrictModuleSection g F sV)) :
    AlgebraicGeometry.Scheme.IdealSheafData.comap
        (sectionZeroIdealOfFreeIso I eU sU) f =
      AlgebraicGeometry.Scheme.IdealSheafData.comap
        (sectionZeroIdealOfFreeIso I eV sV) g := by
  rw [sectionZeroIdealOfFreeIso_comap_eq_canonicalRestriction f I eU sU,
    sectionZeroIdealOfFreeIso_comap_eq_canonicalRestriction g I eV sV]
  let eL := restrictionFreeIsoOf f I eU
  let eR := restrictionFreeIsoOf g I eV
  let sL := restrictModuleSection f E sU
  let sR := restrictModuleSection g F sV
  change sectionZeroIdealOfFreeIso I eL sL =
    sectionZeroIdealOfFreeIso I eR sR
  calc
    sectionZeroIdealOfFreeIso I eL sL =
        sectionZeroIdealOfFreeIso I (eL ≪≫ α)
          (SheafOfModules.sectionsMap α.hom sL) :=
      sectionZeroIdealOfFreeIso_postcompose_eq I eL α sL
    _ = sectionZeroIdealOfFreeIso I (eL ≪≫ α) (scaleSection a sR) := by
      rw [hsection]
    _ = sectionZeroIdealOfFreeIso I (eL ≪≫ α) sR :=
      sectionZeroIdealOfFreeIso_scaleSection_eq_of_isIso I (eL ≪≫ α) a sR
    _ = sectionZeroIdealOfFreeIso I eR sR :=
      sectionZeroIdealOfFreeIso_eq_of_finiteFreeIso I I (eL ≪≫ α) eR sR

/-- Given the canonical identification between the two restricted chart
modules, its compatibility with a section yields the pullback formula for
the local zero ideal. -/
theorem localSectionZeroIdealOfOver_comap_eq_restrictFreeIsoOver_of_sectionCompatibility
    {X : Scheme.{u}} {E : X.Modules} {U V : X.Opens} (f : V ⟶ U)
    [AlgebraicGeometry.IsAffine (U : Scheme.{u})]
    [AlgebraicGeometry.IsAffine (V : Scheme.{u})]
    (I : Type u) [Fintype I] [DecidableEq I]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ E.over U)
    (s : E.sections)
    (hsection : SheafOfModules.sectionsMap
      (localRestrictionTargetIso (E := E) f).inv
      (restrictModuleSection (X.homOfLE (leOfHom f))
        ((AlgebraicGeometry.Scheme.Modules.overEquiv U).functor.obj (E.over U))
        (restrictSectionToOpen (X := X) U s)) =
      restrictSectionToOpen (X := X) V s) :
    AlgebraicGeometry.Scheme.IdealSheafData.comap
      (localSectionZeroIdealOfOver (X := X) U I t s)
      (X.homOfLE (leOfHom f)) =
    localSectionZeroIdealOfOver (X := X) V I
      (restrictFreeIsoOver (X := X) f I t) s := by
  let h := X.homOfLE (leOfHom f)
  let eU := localFreeIsoOfOver (X := X) U I t
  let eC := restrictionFreeIsoOf h I eU
  let g : (AlgebraicGeometry.Scheme.Modules.overEquiv V).functor.obj (E.over V) ≅
      (AlgebraicGeometry.Scheme.Modules.restrictFunctor h).obj
        ((AlgebraicGeometry.Scheme.Modules.overEquiv U).functor.obj (E.over U)) :=
    localRestrictionTargetIso (E := E) f
  let sU := restrictSectionToOpen (X := X) U s
  let sC := restrictModuleSection h
    ((AlgebraicGeometry.Scheme.Modules.overEquiv U).functor.obj (E.over U)) sU
  let sV := restrictSectionToOpen (X := X) V s
  let eV := localFreeIsoOfOver (X := X) V I
    (restrictFreeIsoOver (X := X) f I t)
  change AlgebraicGeometry.Scheme.IdealSheafData.comap
      (sectionZeroIdealOfFreeIso I eU sU) h =
    sectionZeroIdealOfFreeIso I eV sV
  rw [sectionZeroIdealOfFreeIso_comap_eq_canonicalRestriction h I eU sU]
  change sectionZeroIdealOfFreeIso I eC sC =
    sectionZeroIdealOfFreeIso I eV sV
  rw [sectionZeroIdealOfFreeIso_postcompose_eq I eC g.symm sC]
  rw [show SheafOfModules.sectionsMap g.symm.hom sC = sV from hsection]
  exact sectionZeroIdealOfFreeIso_eq_of_finiteFreeIso I I (eC ≪≫ g.symm) eV sV

/-- The nested-chart pullback formula needs only the reduced unit coherence
from `localRestrictionUnitCompatible_iff`; the section comparison is supplied
by `localRestrictionTargetIso_sectionCompatibility_of_core`. -/
theorem localSectionZeroIdealOfOver_comap_eq_restrictFreeIsoOver_of_core
    {X : Scheme.{u}} {E : X.Modules} {U V : X.Opens} (f : V ⟶ U)
    [AlgebraicGeometry.IsAffine (U : Scheme.{u})]
    [AlgebraicGeometry.IsAffine (V : Scheme.{u})]
    (I : Type u) [Fintype I] [DecidableEq I]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ E.over U)
    (s : E.sections)
    (hcore :
      (AlgebraicGeometry.Scheme.Modules.restrictUnitIso
        (X.homOfLE (leOfHom f))).symm.hom ≫
        (AlgebraicGeometry.Scheme.Modules.overMapCompOverEquiv f).inv.app
          ((SheafOfModules.unit X.ringCatSheaf).over U) = 𝟙 _) :
    AlgebraicGeometry.Scheme.IdealSheafData.comap
      (localSectionZeroIdealOfOver (X := X) U I t s)
      (X.homOfLE (leOfHom f)) =
    localSectionZeroIdealOfOver (X := X) V I
      (restrictFreeIsoOver (X := X) f I t) s := by
  exact localSectionZeroIdealOfOver_comap_eq_restrictFreeIsoOver_of_sectionCompatibility
    f I t s (localRestrictionTargetIso_sectionCompatibility_of_core f hcore s)

/-- Coordinate zero ideals of canonically restricted sections commute with
pullback along nested affine charts. -/
theorem localSectionZeroIdealOfOver_comap_eq_restrictFreeIsoOver
    {X : Scheme.{u}} {E : X.Modules} {U V : X.Opens} (f : V ⟶ U)
    [AlgebraicGeometry.IsAffine (U : Scheme.{u})]
    [AlgebraicGeometry.IsAffine (V : Scheme.{u})]
    (I : Type u) [Fintype I] [DecidableEq I]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ E.over U)
    (s : E.sections) :
    AlgebraicGeometry.Scheme.IdealSheafData.comap
      (localSectionZeroIdealOfOver (X := X) U I t s)
      (X.homOfLE (leOfHom f)) =
    localSectionZeroIdealOfOver (X := X) V I
      (restrictFreeIsoOver (X := X) f I t) s := by
  exact localSectionZeroIdealOfOver_comap_eq_restrictFreeIsoOver_of_core
    f I t s (localRestrictionUnitCore f)

/-- A morphism-level compatibility formula for every free coordinate implies
the pullback formula for the coordinate zero ideal.  This is the form in
which the calculation for the canonical restriction of a free
trivialization will be used. -/
theorem freeSectionZeroIdeal_comap_eq_of_coordinate_homs
    {X Y : Scheme.{u}} [AlgebraicGeometry.IsAffine X] [AlgebraicGeometry.IsAffine Y]
    (f : X ⟶ Y) [IsOpenImmersion f] (I : Type u)
    (s : (SheafOfModules.free (R := Y.ringCatSheaf) I).sections)
    (t : (SheafOfModules.free (R := X.ringCatSheaf) I).sections)
    (h : ∀ i,
      (SheafOfModules.free (R := X.ringCatSheaf) I).unitHomEquiv.symm t ≫
          freeCoordinateMap (X := X) I i =
        (AlgebraicGeometry.Scheme.Modules.restrictUnitIso f).inv ≫
          (AlgebraicGeometry.Scheme.Modules.restrictFunctor f).map
            ((SheafOfModules.free (R := Y.ringCatSheaf) I).unitHomEquiv.symm s ≫
              freeCoordinateMap (X := Y) I i) ≫
          (AlgebraicGeometry.Scheme.Modules.restrictUnitIso f).hom) :
    AlgebraicGeometry.Scheme.IdealSheafData.comap
      (freeSectionZeroIdeal (X := Y) I s) f =
      freeSectionZeroIdeal (X := X) I t := by
  apply freeSectionZeroIdeal_comap_eq_of_coordinate_restrict f I s t
  intro i
  exact freeSectionCoordinate_restrict_eq_appTop_of_hom f I s t i (h i)

/-- The preceding affine restriction calculation is invariant under a chosen
free trivialization.  This is the form used by a local trivialization of the
Serre bundle: it reduces compatibility of zero ideals to compatibility of the
scalar coordinates of the restricted section. -/
theorem sectionZeroIdealOfFreeIso_comap_eq_of_coordinate_restrict
    {X Y : Scheme.{u}} [AlgebraicGeometry.IsAffine X] [AlgebraicGeometry.IsAffine Y]
    (f : X ⟶ Y) [IsOpenImmersion f] {E : Y.Modules} {F : X.Modules}
    (I : Type u)
    (e : SheafOfModules.free (R := Y.ringCatSheaf) I ≅ E)
    (g : SheafOfModules.free (R := X.ringCatSheaf) I ≅ F)
    (s : E.sections) (t : F.sections)
    (h : ∀ i, sectionCoordinateOfFreeIso (X := X) I g t i =
      f.appTop (sectionCoordinateOfFreeIso (X := Y) I e s i)) :
    AlgebraicGeometry.Scheme.IdealSheafData.comap
      (sectionZeroIdealOfFreeIso (X := Y) I e s) f =
      sectionZeroIdealOfFreeIso (X := X) I g t := by
  unfold sectionZeroIdealOfFreeIso
  apply freeSectionZeroIdeal_comap_eq_of_coordinate_restrict f I
    (SheafOfModules.sectionsMap e.inv s) (SheafOfModules.sectionsMap g.inv t)
  intro i
  simpa only [sectionCoordinateOfFreeIso] using h i

/-- A local free presentation gives compatible zero ideals across an affine
open inclusion as soon as its scalar-coordinate restriction formula is known.
The conclusion is stated in the over-site language used for the rank-two
Serre-pencil charts. -/
theorem localSectionZeroIdealOfOver_comap_eq_of_coordinate_restrict
    {X : Scheme.{u}} {U V : X.Opens} (f : V ⟶ U)
    [AlgebraicGeometry.IsAffine (U : Scheme.{u})]
    [AlgebraicGeometry.IsAffine (V : Scheme.{u})]
    {E : X.Modules} (I : Type u)
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ E.over U)
    (v : SheafOfModules.free (R := X.ringCatSheaf.over V) I ≅ E.over V)
    (s : E.sections)
    (h : ∀ i,
      sectionCoordinateOfFreeIso (X := (V : Scheme.{u})) I
        (localFreeIsoOfOver (X := X) V I v)
        (restrictSectionToOpen (X := X) V s) i =
      (X.homOfLE (leOfHom f)).appTop
        (sectionCoordinateOfFreeIso (X := (U : Scheme.{u})) I
          (localFreeIsoOfOver (X := X) U I t)
          (restrictSectionToOpen (X := X) U s) i)) :
    AlgebraicGeometry.Scheme.IdealSheafData.comap
      (localSectionZeroIdealOfOver (X := X) U I t s)
      (X.homOfLE (leOfHom f)) =
      localSectionZeroIdealOfOver (X := X) V I v s := by
  unfold localSectionZeroIdealOfOver
  exact sectionZeroIdealOfFreeIso_comap_eq_of_coordinate_restrict
    (X.homOfLE (leOfHom f)) I
    (localFreeIsoOfOver (X := X) U I t)
    (localFreeIsoOfOver (X := X) V I v)
    (restrictSectionToOpen (X := X) U s)
    (restrictSectionToOpen (X := X) V s) h

end PfaffianDescent.BundleSectionZeroLocus
