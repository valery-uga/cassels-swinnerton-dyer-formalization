import PfaffianDescent.CorayOriginalOpenSections
import PfaffianDescent.CorayOpenRestrictPushforwardUnit
import PfaffianDescent.CorayAffineTopCokernelProjection

/-! Actual unit-cokernel affine comparisons for arbitrary affine morphisms.
This generalizes only formal unit/restriction/cokernel constructions; no
normalization morphism or normalization quotient is substituted for f. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The original global quotient SHEAF restricts to the actual quotient SHEAF
for the SAME original morphism restricted to U. This is a genuine
sheaf-level comparison, obtained from proved unit-map compatibility and
restriction preservation of cokernels, not a section comparison premise. -/
def unitCokernelSheaf_restrictIso
    {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) :
    (Scheme.Modules.restrictFunctor U.ι).obj (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) ≅
      cokernel (SheafOfModules.unitToPushforwardObjUnit
        (f ∣_ U).toRingCatSheafHom) := by
  let ν := f
  let F := Scheme.Modules.restrictFunctor U.ι
  let q := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let qU := SheafOfModules.unitToPushforwardObjUnit (ν ∣_ U).toRingCatSheafHom
  letI : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint F
  change F.obj (cokernel q) ≅ cokernel qU
  exact PreservesCokernel.iso F q ≪≫
    cokernel.mapIso (F.map q) qU (Scheme.Modules.restrictUnitIso U.ι)
      (openRestrictPushforwardUnitIso ν U) (openRestrictPushforwardUnitIso_unit ν U)

/-- The global restriction comparison preserves the actual quotient
projection from the actual source pushforward on this ORIGINAL open. -/
theorem unitCokernelSheaf_restrictIso_π
    {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) :
    (Scheme.Modules.restrictFunctor U.ι).map
      (cokernel.π (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) ≫
        (unitCokernelSheaf_restrictIso f U).hom =
      (openRestrictPushforwardUnitIso
        f U).hom ≫
      cokernel.π (SheafOfModules.unitToPushforwardObjUnit
        (f ∣_ U).toRingCatSheafHom) := by
  let ν := f
  let F := Scheme.Modules.restrictFunctor U.ι
  let q := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let qU := SheafOfModules.unitToPushforwardObjUnit (ν ∣_ U).toRingCatSheafHom
  letI : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint F
  change F.map (cokernel.π q) ≫
    (PreservesCokernel.iso F q ≪≫
      cokernel.mapIso (F.map q) qU (Scheme.Modules.restrictUnitIso U.ι)
        (openRestrictPushforwardUnitIso ν U) (openRestrictPushforwardUnitIso_unit ν U)).hom = _
  let e := cokernel.mapIso (F.map q) qU (Scheme.Modules.restrictUnitIso U.ι)
    (openRestrictPushforwardUnitIso ν U) (openRestrictPushforwardUnitIso_unit ν U)
  calc
    _ = (F.map (cokernel.π q) ≫ (PreservesCokernel.iso F q).hom) ≫ e.hom :=
      (Category.assoc _ _ _).symm
    _ = cokernel.π (F.map q) ≫ e.hom :=
      congrArg (fun t => t ≫ e.hom) (PreservesCokernel.π_iso_hom F q)
    _ = _ := cokernel.π_desc _ _ _

/-- ACTUAL affine sections of the ACTUAL global unit cokernel
SHEAF agree with the cokernel of the ACTUAL original linear section map.
This exactness comparison is constructed from restriction, actual affine
source and target transport, and scalar restriction; it is not a premise. -/
def unitCokernelSheaf_affineSectionCokernelIso
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f]
    (U : X.Opens) (hU : IsAffineOpen U) :
    (schemeOpenModuleFunctor X U).obj (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) ≅
      cokernel ((schemeOpenModuleFunctor X U).map
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) := by
  let ν := f
  letI : Algebra Γ(X, U) Γ(Y, ν ⁻¹ᵁ U) :=
    (ν.app U).hom.toAlgebra
  letI : IsAffine U.toScheme := hU
  letI : IsAffine (ν ⁻¹ᵁ U).toScheme := hU.preimage f
  let F := Scheme.Modules.restrictFunctor U.ι
  let T := schemeTopModuleFunctor U.toScheme
  let S := ModuleCat.restrictScalars U.topIso.inv.hom
  let H := T ⋙ S
  let G := schemeOpenModuleFunctor X U
  let E := originalOpenRestrictTopSectionsNatIso X U
  let OX := SheafOfModules.unit X.ringCatSheaf
  let N := (Scheme.Modules.pushforward ν).obj
    (SheafOfModules.unit Y.ringCatSheaf)
  let q := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let qU := SheafOfModules.unitToPushforwardObjUnit (ν ∣_ U).toRingCatSheafHom
  let eUnit := Scheme.Modules.restrictUnitIso U.ι
  let ePush := openRestrictPushforwardUnitIso ν U
  let eA := H.mapIso eUnit.symm ≪≫ E.app OX
  let eB := H.mapIso ePush.symm ≪≫ E.app N
  have hcomp : qU ≫ ePush.inv = eUnit.inv ≫ F.map q := by
    apply (cancel_mono ePush.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hu : F.map q ≫ ePush.hom = eUnit.hom ≫ qU :=
      openRestrictPushforwardUnitIso_unit ν U
    rw [hu]
    simp
  have hc : H.map qU ≫ eB.hom = eA.hom ≫ G.map q := by
    change H.map qU ≫ (H.map ePush.inv ≫ E.hom.app N) =
      (H.map eUnit.inv ≫ E.hom.app OX) ≫ G.map q
    rw [← Category.assoc, ← H.map_comp, hcomp, H.map_comp, Category.assoc]
    have hn : H.map (F.map q) ≫ E.hom.app N = E.hom.app OX ≫ G.map q :=
      E.hom.naturality q
    rw [hn, Category.assoc]
  let eSections := S.mapIso
    (T.mapIso (unitCokernelSheaf_restrictIso f U) ≪≫
      affineTargetQuotientSheaf_topCokernelIso (ν ∣_ U)) ≪≫
    PreservesCokernel.iso S (T.map qU)
  exact (E.app (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom))).symm ≪≫ eSections ≪≫
    cokernel.mapIso (H.map qU) (G.map q) eA eB hc


private theorem mappedIso_conjugate_cancel
    {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {A B : C} (e : A ≅ B) {Z : D} (d : G.obj A ≅ Z) :
    d.inv ≫ G.map e.hom ≫ (G.map e.inv ≫ d.hom) = 𝟙 Z := by
  rw [← Functor.map_comp_assoc, e.hom_inv_id, G.map_id,
    Category.id_comp, Iso.inv_hom_id]

private theorem mappedProjectionComposite
    {C D E : Type*} [Category C] [Category D] [Category E]
    (T : C ⥤ D) (S : D ⥤ E)
    {A B C0 C1 : C} (f : A ⟶ B) (u : A ⟶ C0)
    (v : B ≅ C1) (w : C0 ⟶ C1)
    {D0 : D} (e : T.obj C1 ≅ D0) (t : T.obj C0 ⟶ D0)
    {E0 : E} (d : S.obj D0 ≅ E0) (s : S.obj (T.obj C0) ⟶ E0)
    (h : f ≫ v.hom = u ≫ w) (ht : T.map w ≫ e.hom = t)
    (hs : S.map t ≫ d.hom = s) :
    (T ⋙ S).map f ≫ (S.mapIso (T.mapIso v ≪≫ e) ≪≫ d).hom =
      (T ⋙ S).map u ≫ s := by
  calc
    (T ⋙ S).map f ≫ (S.mapIso (T.mapIso v ≪≫ e) ≪≫ d).hom =
        S.map ((T.map f ≫ T.map v.hom) ≫ e.hom) ≫ d.hom := by
          simp only [Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom,
            Functor.map_comp, Category.assoc]
    _ = S.map ((T.map u ≫ T.map w) ≫ e.hom) ≫ d.hom := by
          rw [← T.map_comp, h, T.map_comp]
    _ = S.map (T.map u ≫ t) ≫ d.hom := by
          rw [Category.assoc, ht]
    _ = (T ⋙ S).map u ≫ s := by
          rw [S.map_comp, Category.assoc, hs]
          rfl


private theorem projectionComparisonCancel
    {C : Type*} [Category C] {X Y Z W T U V : C}
    (f : X ⟶ Y) (e : Y ⟶ Z) (p : Z ⟶ W) (c : W ⟶ V)
    (n : X ⟶ T) (a : T ⟶ Z) (b : T ⟶ U) (q : U ⟶ W)
    (v : U ⟶ X) (t : X ⟶ V)
    (hn : f ≫ e = n ≫ a) (hs : a ≫ p = b ≫ q)
    (hm : q ≫ c = v ≫ t) (hc : n ≫ b ≫ v = 𝟙 X) :
    f ≫ ((e ≫ p) ≫ c) = t := by
  calc
    f ≫ ((e ≫ p) ≫ c) = (f ≫ e) ≫ p ≫ c := by simp only [Category.assoc]
    _ = (n ≫ a) ≫ p ≫ c := by rw [hn]
    _ = n ≫ (a ≫ p) ≫ c := by simp only [Category.assoc]
    _ = n ≫ (b ≫ q) ≫ c := by rw [hs]
    _ = n ≫ b ≫ (q ≫ c) := by simp only [Category.assoc]
    _ = n ≫ b ≫ (v ≫ t) := by rw [hm]
    _ = (n ≫ b ≫ v) ≫ t := by simp only [Category.assoc]
    _ = t := by rw [hc, Category.id_comp]


/-- The constructed ACTUAL global quotient-section comparison sends the
ACTUAL sheaf quotient projection to the ACTUAL original linear section
cokernel projection. The restricted-map and scalar transports are all proved. -/
theorem unitCokernelSheaf_affineSectionCokernelIso_π
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f]
    (U : X.Opens) (hU : IsAffineOpen U) :
    (schemeOpenModuleFunctor X U).map
      (cokernel.π (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) ≫
        (unitCokernelSheaf_affineSectionCokernelIso f U hU).hom =
      cokernel.π ((schemeOpenModuleFunctor X U).map
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) := by
  let ν := f
  letI : Algebra Γ(X, U) Γ(Y, ν ⁻¹ᵁ U) :=
    (ν.app U).hom.toAlgebra
  letI : IsAffine U.toScheme := hU
  letI : IsAffine (ν ⁻¹ᵁ U).toScheme := hU.preimage f
  let F := Scheme.Modules.restrictFunctor U.ι
  let T := schemeTopModuleFunctor U.toScheme
  let S := ModuleCat.restrictScalars U.topIso.inv.hom
  let H := T ⋙ S
  let G := schemeOpenModuleFunctor X U
  let E := originalOpenRestrictTopSectionsNatIso X U
  let OX := SheafOfModules.unit X.ringCatSheaf
  let N := (Scheme.Modules.pushforward ν).obj
    (SheafOfModules.unit Y.ringCatSheaf)
  let q := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let qU := SheafOfModules.unitToPushforwardObjUnit (ν ∣_ U).toRingCatSheafHom
  let eUnit := Scheme.Modules.restrictUnitIso U.ι
  let ePush := openRestrictPushforwardUnitIso ν U
  let eA := H.mapIso eUnit.symm ≪≫ E.app OX
  let eB := H.mapIso ePush.symm ≪≫ E.app N
  have hcomp : qU ≫ ePush.inv = eUnit.inv ≫ F.map q := by
    apply (cancel_mono ePush.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hu : F.map q ≫ ePush.hom = eUnit.hom ≫ qU :=
      openRestrictPushforwardUnitIso_unit ν U
    rw [hu]
    simp
  have hc : H.map qU ≫ eB.hom = eA.hom ≫ G.map q := by
    change H.map qU ≫ (H.map ePush.inv ≫ E.hom.app N) =
      (H.map eUnit.inv ≫ E.hom.app OX) ≫ G.map q
    rw [← Category.assoc, ← H.map_comp, hcomp, H.map_comp, Category.assoc]
    have hn : H.map (F.map q) ≫ E.hom.app N = E.hom.app OX ≫ G.map q :=
      E.hom.naturality q
    rw [hn, Category.assoc]
  let eRestr := unitCokernelSheaf_restrictIso f U
  let eTop := affineTargetQuotientSheaf_topCokernelIso (ν ∣_ U)
  let ePres := PreservesCokernel.iso S (T.map qU)
  let eSections := S.mapIso (T.mapIso eRestr ≪≫ eTop) ≪≫ ePres
  let eC := cokernel.mapIso (H.map qU) (G.map q) eA eB hc
  have hdef : (unitCokernelSheaf_affineSectionCokernelIso f U hU).hom =
      ((E.app (cokernel q)).inv ≫ eSections.hom) ≫ eC.hom := by
    rfl
  have hsections : H.map (F.map (cokernel.π q)) ≫ eSections.hom =
      H.map ePush.hom ≫ cokernel.π (H.map qU) := by
    have hr : F.map (cokernel.π q) ≫ eRestr.hom =
        ePush.hom ≫ cokernel.π qU :=
      unitCokernelSheaf_restrictIso_π f U
    have ht : T.map (cokernel.π qU) ≫ eTop.hom =
        cokernel.π (T.map qU) :=
      affineTargetQuotientSheaf_topCokernelIso_π (ν ∣_ U)
    have hs : S.map (cokernel.π (T.map qU)) ≫ ePres.hom =
        cokernel.π (S.map (T.map qU)) :=
      PreservesCokernel.π_iso_hom S (T.map qU)
    exact mappedProjectionComposite T S (F.map (cokernel.π q)) ePush.hom
      eRestr (cokernel.π qU) eTop (cokernel.π (T.map qU))
      ePres (cokernel.π (S.map (T.map qU))) hr ht hs

  have hnat : G.map (cokernel.π q) ≫ (E.app (cokernel q)).inv =
      (E.app N).inv ≫ H.map (F.map (cokernel.π q)) := by
    exact E.inv.naturality (cokernel.π q)
  have hmap : cokernel.π (H.map qU) ≫ eC.hom =
      eB.hom ≫ cokernel.π (G.map q) := cokernel.π_desc _ _ _
  have hcancel : (E.app N).inv ≫ H.map ePush.hom ≫ eB.hom = 𝟙 (G.obj N) := by
    change (E.app N).inv ≫ H.map ePush.hom ≫ (H.map ePush.inv ≫ (E.app N).hom) = _
    exact mappedIso_conjugate_cancel H ePush (E.app N)
  change G.map (cokernel.π q) ≫
    (unitCokernelSheaf_affineSectionCokernelIso f U hU).hom =
    cokernel.π (G.map q)
  exact (congrArg (fun z => G.map (cokernel.π q) ≫ z) hdef).trans
    (projectionComparisonCancel (G.map (cokernel.π q))
      (E.app (cokernel q)).inv eSections.hom eC.hom
      (E.app N).inv (H.map (F.map (cokernel.π q)))
      (H.map ePush.hom) (cokernel.π (H.map qU))
      eB.hom (cokernel.π (G.map q)) hnat hsections hmap hcancel)



end PfaffianDescent.Coray
