import PfaffianDescent.CorayGenericNormalizationQuotientAffineSections
import PfaffianDescent.CorayAffineTopCokernelProjection

/-! Projection compatibility for ACTUAL affine sections of the ACTUAL global
normalization quotient sheaf. No section-comparison or projection certificate.
STATUS: UNVERIFIED source only. Root owns all compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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
theorem genericNormalizationQuotientSheaf_affineSectionCokernelIso_π
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    (schemeOpenModuleFunctor X U).map
      (cokernel.π (genericNormalizationUnitToPushforwardUnit X)) ≫
        (genericNormalizationQuotientSheaf_affineSectionCokernelIso X U hU).hom =
      cokernel.π ((schemeOpenModuleFunctor X U).map
        (genericNormalizationUnitToPushforwardUnit X)) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : Algebra Γ(X, U) Γ((X.fromSpecStalk (genericPoint X)).normalization, ν ⁻¹ᵁ U) :=
    (ν.app U).hom.toAlgebra
  letI : IsAffine U.toScheme := hU
  letI : IsAffine (ν ⁻¹ᵁ U).toScheme := genericNormalization_affinePreimage_isAffine X U hU
  let F := Scheme.Modules.restrictFunctor U.ι
  let T := schemeTopModuleFunctor U.toScheme
  let S := ModuleCat.restrictScalars U.topIso.inv.hom
  let H := T ⋙ S
  let G := schemeOpenModuleFunctor X U
  let E := originalOpenRestrictTopSectionsNatIso X U
  let OX := SheafOfModules.unit X.ringCatSheaf
  let N := (Scheme.Modules.pushforward ν).obj
    (SheafOfModules.unit (X.fromSpecStalk (genericPoint X)).normalization.ringCatSheaf)
  let q := genericNormalizationUnitToPushforwardUnit X
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
  let eRestr := genericNormalizationQuotientSheaf_restrictIso X U
  let eTop := affineTargetQuotientSheaf_topCokernelIso (ν ∣_ U)
  let ePres := PreservesCokernel.iso S (T.map qU)
  let eSections := S.mapIso (T.mapIso eRestr ≪≫ eTop) ≪≫ ePres
  let eC := cokernel.mapIso (H.map qU) (G.map q) eA eB hc
  have hdef : (genericNormalizationQuotientSheaf_affineSectionCokernelIso X U hU).hom =
      ((E.app (cokernel q)).inv ≫ eSections.hom) ≫ eC.hom := by
    rfl
  have hsections : H.map (F.map (cokernel.π q)) ≫ eSections.hom =
      H.map ePush.hom ≫ cokernel.π (H.map qU) := by
    have hr : F.map (cokernel.π q) ≫ eRestr.hom =
        ePush.hom ≫ cokernel.π qU :=
      genericNormalizationQuotientSheaf_restrictIso_π X U
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
    (genericNormalizationQuotientSheaf_affineSectionCokernelIso X U hU).hom =
    cokernel.π (G.map q)
  exact (congrArg (fun z => G.map (cokernel.π q) ≫ z) hdef).trans
    (projectionComparisonCancel (G.map (cokernel.π q))
      (E.app (cokernel q)).inv eSections.hom eC.hom
      (E.app N).inv (H.map (F.map (cokernel.π q)))
      (H.map ePush.hom) (cokernel.π (H.map qU))
      eB.hom (cokernel.π (G.map q)) hnat hsections hmap hcancel)


/-- The ACTUAL affine sections of the ACTUAL global quotient sheaf retain
its literal original integral-closure quotient projection, not only its rank. -/
theorem genericNormalizationQuotientSheaf_affineSectionsIso_π
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    letI : Algebra Γ(X, U)
      Γ((X.fromSpecStalk (genericPoint X)).normalization,
        (X.fromSpecStalk (genericPoint X)).fromNormalization ⁻¹ᵁ U) :=
      ((X.fromSpecStalk (genericPoint X)).fromNormalization.app U).hom.toAlgebra
    (schemeOpenModuleFunctor X U).map
      (cokernel.π (genericNormalizationUnitToPushforwardUnit X)) ≫
        (genericNormalizationQuotientSheaf_affineSectionsIso X U hU).hom =
      (genericNormalization_preimageSectionsAlgEquiv X U hU).toLinearEquiv.toModuleIso.hom ≫
        ModuleCat.ofHom
          (LinearMap.range (Algebra.linearMap Γ(X, U)
            (integralClosure Γ(X, U) X.functionField))).mkQ := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  letI : Algebra Γ(X, U)
      Γ((X.fromSpecStalk (genericPoint X)).normalization,
        (X.fromSpecStalk (genericPoint X)).fromNormalization ⁻¹ᵁ U) :=
    ((X.fromSpecStalk (genericPoint X)).fromNormalization.app U).hom.toAlgebra
  change (schemeOpenModuleFunctor X U).map
      (cokernel.π (genericNormalizationUnitToPushforwardUnit X)) ≫
        (genericNormalizationQuotientSheaf_affineSectionCokernelIso X U hU ≪≫
          genericNormalization_affineSectionCokernelIso X U hU).hom = _
  rw [Iso.trans_hom, ← Category.assoc,
    genericNormalizationQuotientSheaf_affineSectionCokernelIso_π]
  exact genericNormalization_affineSectionCokernelIso_π X U hU

end PfaffianDescent.Coray
