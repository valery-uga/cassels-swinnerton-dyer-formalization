import PfaffianDescent.FlatClosedImmersionSequence
import PfaffianDescent.SheafModulePushforwardExact

/-! Comparing closed-immersion quotient pushforwards on affine target charts. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- The pushforward structure sheaf of a closed immersion is canonically
the cokernel of its actual ideal-module inclusion. -/
noncomputable def closedImmersionPushforwardCokernelIso
    {Y Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i] :
    cokernel (IdealSheafDataModule.closedImmersionModuleToUnit i) ≅
      (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf) := by
  let S := IdealSheafDataModule.closedImmersionModulePushforwardSequence i
  change cokernel S.f ≅ S.X₃
  have hS := IdealSheafDataModule.closedImmersionModulePushforwardSequence_shortExact i
  haveI : Epi S.g := hS.epi_g
  exact IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    hS.exact.gIsCokernel

theorem closedImmersionPushforwardCokernelIso_π
    {Y Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i] :
    cokernel.π (IdealSheafDataModule.closedImmersionModuleToUnit i) ≫
      (closedImmersionPushforwardCokernelIso i).hom =
      IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i := by
  let S := IdealSheafDataModule.closedImmersionModulePushforwardSequence i
  have hS := IdealSheafDataModule.closedImmersionModulePushforwardSequence_shortExact i
  haveI : Epi S.g := hS.epi_g
  change cokernel.π S.f ≫
    (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
      hS.exact.gIsCokernel).hom = S.g
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit _) hS.exact.gIsCokernel WalkingParallelPair.one

/-- Restriction of the closed-immersion pushforward to a target affine
chart is the cokernel of the restricted actual ideal inclusion. -/
noncomputable def targetAffineChartRestrictPushforwardCokernelIso
    {Y Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : Y.affineCover.I₀) :
    let u := Y.affineCover.f a
    cokernel ((Scheme.Modules.restrictFunctor u).map
      (IdealSheafDataModule.closedImmersionModuleToUnit i)) ≅
      (Scheme.Modules.restrictFunctor u).obj
        ((Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)) := by
  let u := Y.affineCover.f a
  let R := Scheme.Modules.restrictFunctor u
  let S := IdealSheafDataModule.closedImmersionModulePushforwardSequence i
  change cokernel (S.map R).f ≅ (S.map R).X₃
  have hS := IdealSheafDataModule.closedImmersionModulePushforwardSequence_shortExact i
  have hR := ShortComplex.shortExact_map_restrictFunctor u S hS
  haveI : Epi (S.map R).g := hR.epi_g
  exact IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    hR.exact.gIsCokernel

theorem targetAffineChartRestrictPushforwardCokernelIso_π
    {Y Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : Y.affineCover.I₀) :
    let u := Y.affineCover.f a
    cokernel.π ((Scheme.Modules.restrictFunctor u).map
      (IdealSheafDataModule.closedImmersionModuleToUnit i)) ≫
      (targetAffineChartRestrictPushforwardCokernelIso i a).hom =
      (Scheme.Modules.restrictFunctor u).map
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) := by
  let u := Y.affineCover.f a
  let R := Scheme.Modules.restrictFunctor u
  let S := IdealSheafDataModule.closedImmersionModulePushforwardSequence i
  have hS := IdealSheafDataModule.closedImmersionModulePushforwardSequence_shortExact i
  have hR := ShortComplex.shortExact_map_restrictFunctor u S hS
  haveI : Epi (S.map R).g := hR.epi_g
  change cokernel.π (S.map R).f ≫
    (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
      hR.exact.gIsCokernel).hom = (S.map R).g
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit _) hR.exact.gIsCokernel WalkingParallelPair.one

/-- The actual ideal-module comparison on a target chart induces an
isomorphism between the cokernels of the two ideal inclusions. -/
noncomputable def targetAffineChartIdealCokernelIso
    {Y Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : Y.affineCover.I₀) :
    let u := Y.affineCover.f a
    let iU := pullback.fst u i
    cokernel ((Scheme.Modules.restrictFunctor u).map
      (IdealSheafDataModule.closedImmersionModuleToUnit i)) ≅
      cokernel (IdealSheafDataModule.closedImmersionModuleToUnit iU) := by
  let u := Y.affineCover.f a
  let iU := pullback.fst u i
  let R := Scheme.Modules.restrictFunctor u
  let e : IdealSheafDataModule.closedImmersionModule iU ≅
      R.obj (IdealSheafDataModule.closedImmersionModule i) :=
    targetAffineChartIdealModule_moduleIso i a
  let t := Scheme.Modules.restrictUnitIso u
  have h : e.hom ≫ R.map
      (IdealSheafDataModule.closedImmersionModuleToUnit i) ≫ t.hom =
      IdealSheafDataModule.closedImmersionModuleToUnit iU :=
    targetAffineChartIdealModule_moduleIso_toUnit i a
  have h' : R.map (IdealSheafDataModule.closedImmersionModuleToUnit i) ≫ t.hom =
      e.inv ≫ IdealSheafDataModule.closedImmersionModuleToUnit iU := by
    apply (e.eq_inv_comp).2
    exact h
  exact cokernel.mapIso _ _ e.symm t h'

theorem targetAffineChartIdealCokernelIso_π
    {Y Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : Y.affineCover.I₀) :
    let u := Y.affineCover.f a
    let iU := pullback.fst u i
    cokernel.π ((Scheme.Modules.restrictFunctor u).map
      (IdealSheafDataModule.closedImmersionModuleToUnit i)) ≫
      (targetAffineChartIdealCokernelIso i a).hom =
      (Scheme.Modules.restrictUnitIso u).hom ≫
        cokernel.π (IdealSheafDataModule.closedImmersionModuleToUnit iU) := by
  dsimp only [targetAffineChartIdealCokernelIso]
  exact cokernel.π_desc _ _ _

/-- On each target affine chart, restriction of the original quotient
pushforward agrees with the quotient pushforward of the actual fibre-product
closed immersion. -/
noncomputable def targetAffineChartClosedImmersionPushforwardIso
    {Y Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : Y.affineCover.I₀) :
    let u := Y.affineCover.f a
    let iU := pullback.fst u i
    (Scheme.Modules.restrictFunctor u).obj
      ((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)) ≅
      (Scheme.Modules.pushforward iU).obj
        (SheafOfModules.unit (pullback u i).ringCatSheaf) := by
  let u := Y.affineCover.f a
  let iU := pullback.fst u i
  exact (targetAffineChartRestrictPushforwardCokernelIso i a).symm ≪≫
    targetAffineChartIdealCokernelIso i a ≪≫
    closedImmersionPushforwardCokernelIso iU

/-- The chart pushforward isomorphism preserves the actual quotient maps. -/
theorem targetAffineChartClosedImmersionPushforwardIso_quotient
    {Y Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : Y.affineCover.I₀) :
    let u := Y.affineCover.f a
    let iU := pullback.fst u i
    (Scheme.Modules.restrictFunctor u).map
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) ≫
        (targetAffineChartClosedImmersionPushforwardIso i a).hom =
      (Scheme.Modules.restrictUnitIso u).hom ≫
        IdealSheafDataModule.closedImmersionUnitToPushforwardUnit iU := by
  let u := Y.affineCover.f a
  let iU := pullback.fst u i
  let R := Scheme.Modules.restrictFunctor u
  let c := IdealSheafDataModule.closedImmersionModuleToUnit i
  let cU := IdealSheafDataModule.closedImmersionModuleToUnit iU
  let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i
  let qU := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit iU
  let eR := targetAffineChartRestrictPushforwardCokernelIso i a
  let eC := targetAffineChartIdealCokernelIso i a
  let eU := closedImmersionPushforwardCokernelIso iU
  let t := Scheme.Modules.restrictUnitIso u
  have hR : cokernel.π (R.map c) ≫ eR.hom = R.map q :=
    targetAffineChartRestrictPushforwardCokernelIso_π i a
  have hC : cokernel.π (R.map c) ≫ eC.hom = t.hom ≫ cokernel.π cU :=
    targetAffineChartIdealCokernelIso_π i a
  have hU : cokernel.π cU ≫ eU.hom = qU :=
    closedImmersionPushforwardCokernelIso_π iU
  change R.map q ≫ (eR.symm ≪≫ eC ≪≫ eU).hom = t.hom ≫ qU
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [← hR]
  simp only [Category.assoc, eR.hom_inv_id_assoc]
  change cokernel.π (R.map c) ≫ eC.hom ≫ eU.hom = t.hom ≫ qU
  calc
    cokernel.π (R.map c) ≫ eC.hom ≫ eU.hom =
        (cokernel.π (R.map c) ≫ eC.hom) ≫ eU.hom :=
      (Category.assoc _ _ _).symm
    _ = (t.hom ≫ cokernel.π cU) ≫ eU.hom :=
      congrArg (· ≫ eU.hom) hC
    _ = t.hom ≫ (cokernel.π cU ≫ eU.hom) := Category.assoc _ _ _
    _ = t.hom ≫ qU := congrArg (t.hom ≫ ·) hU

/-- A quotient-compatible morphism on a target chart is unique. This is
the coherence fact needed when comparing the constructions on overlaps. -/
theorem targetAffineChartClosedImmersionPushforwardHom_unique
    {Y Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (a : Y.affineCover.I₀)
    (h₁ h₂ :
      (Scheme.Modules.restrictFunctor (Y.affineCover.f a)).obj
        ((Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)) ⟶
      (Scheme.Modules.pushforward
        (pullback.fst (Y.affineCover.f a) i)).obj
          (SheafOfModules.unit
            (pullback (Y.affineCover.f a) i).ringCatSheaf))
    (h₁q : (Scheme.Modules.restrictFunctor (Y.affineCover.f a)).map
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) ≫ h₁ =
      (Scheme.Modules.restrictUnitIso (Y.affineCover.f a)).hom ≫
        IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
          (pullback.fst (Y.affineCover.f a) i))
    (h₂q : (Scheme.Modules.restrictFunctor (Y.affineCover.f a)).map
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) ≫ h₂ =
      (Scheme.Modules.restrictUnitIso (Y.affineCover.f a)).hom ≫
        IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
          (pullback.fst (Y.affineCover.f a) i)) :
    h₁ = h₂ := by
  let R := Scheme.Modules.restrictFunctor (Y.affineCover.f a)
  let S := IdealSheafDataModule.closedImmersionModulePushforwardSequence i
  have hS := IdealSheafDataModule.closedImmersionModulePushforwardSequence_shortExact i
  have hR := ShortComplex.shortExact_map_restrictFunctor
    (Y.affineCover.f a) S hS
  haveI : Epi (R.map (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)) := by
    change Epi (S.map R).g
    exact hR.epi_g
  apply (cancel_epi (R.map
    (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i))).mp
  exact h₁q.trans h₂q.symm

end PfaffianDescent
