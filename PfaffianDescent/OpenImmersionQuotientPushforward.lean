import PfaffianDescent.OpenImmersionIdealModule
import PfaffianDescent.TargetAffineQuotientSheaf

/-! Quotient pushforward comparison along arbitrary open immersions. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- Restriction of the closed-immersion pushforward to a target affine
chart is the cokernel of the restricted actual ideal inclusion. -/
noncomputable def openImmersionRestrictPushforwardCokernelIso
    {Y Z U : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (u : U ⟶ Y) [IsOpenImmersion u] :
        cokernel ((Scheme.Modules.restrictFunctor u).map
      (IdealSheafDataModule.closedImmersionModuleToUnit i)) ≅
      (Scheme.Modules.restrictFunctor u).obj
        ((Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf)) := by
  let R := Scheme.Modules.restrictFunctor u
  let S := IdealSheafDataModule.closedImmersionModulePushforwardSequence i
  change cokernel (S.map R).f ≅ (S.map R).X₃
  have hS := IdealSheafDataModule.closedImmersionModulePushforwardSequence_shortExact i
  have hR := ShortComplex.shortExact_map_restrictFunctor u S hS
  haveI : Epi (S.map R).g := hR.epi_g
  exact IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    hR.exact.gIsCokernel

theorem openImmersionRestrictPushforwardCokernelIso_π
    {Y Z U : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (u : U ⟶ Y) [IsOpenImmersion u] :
        cokernel.π ((Scheme.Modules.restrictFunctor u).map
      (IdealSheafDataModule.closedImmersionModuleToUnit i)) ≫
      (openImmersionRestrictPushforwardCokernelIso i u).hom =
      (Scheme.Modules.restrictFunctor u).map
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) := by
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
noncomputable def openImmersionIdealCokernelIso
    {Y Z U : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (u : U ⟶ Y) [IsOpenImmersion u] :
    let iU := pullback.fst u i
    cokernel ((Scheme.Modules.restrictFunctor u).map
      (IdealSheafDataModule.closedImmersionModuleToUnit i)) ≅
      cokernel (IdealSheafDataModule.closedImmersionModuleToUnit iU) := by
  let iU := pullback.fst u i
  let R := Scheme.Modules.restrictFunctor u
  let e : IdealSheafDataModule.closedImmersionModule iU ≅
      R.obj (IdealSheafDataModule.closedImmersionModule i) :=
    openImmersionIdealModule_moduleIso i u
  let t := Scheme.Modules.restrictUnitIso u
  have h : e.hom ≫ R.map
      (IdealSheafDataModule.closedImmersionModuleToUnit i) ≫ t.hom =
      IdealSheafDataModule.closedImmersionModuleToUnit iU :=
    openImmersionIdealModule_moduleIso_toUnit i u
  have h' : R.map (IdealSheafDataModule.closedImmersionModuleToUnit i) ≫ t.hom =
      e.inv ≫ IdealSheafDataModule.closedImmersionModuleToUnit iU := by
    apply (e.eq_inv_comp).2
    exact h
  exact cokernel.mapIso _ _ e.symm t h'

theorem openImmersionIdealCokernelIso_π
    {Y Z U : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (u : U ⟶ Y) [IsOpenImmersion u] :
    let iU := pullback.fst u i
    cokernel.π ((Scheme.Modules.restrictFunctor u).map
      (IdealSheafDataModule.closedImmersionModuleToUnit i)) ≫
      (openImmersionIdealCokernelIso i u).hom =
      (Scheme.Modules.restrictUnitIso u).hom ≫
        cokernel.π (IdealSheafDataModule.closedImmersionModuleToUnit iU) := by
  dsimp only [openImmersionIdealCokernelIso]
  exact cokernel.π_desc _ _ _

/-- On each target affine chart, restriction of the original quotient
pushforward agrees with the quotient pushforward of the actual fibre-product
closed immersion. -/
noncomputable def openImmersionClosedImmersionPushforwardIso
    {Y Z U : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (u : U ⟶ Y) [IsOpenImmersion u] :
    let iU := pullback.fst u i
    (Scheme.Modules.restrictFunctor u).obj
      ((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)) ≅
      (Scheme.Modules.pushforward iU).obj
        (SheafOfModules.unit (pullback u i).ringCatSheaf) := by
  let iU := pullback.fst u i
  exact (openImmersionRestrictPushforwardCokernelIso i u).symm ≪≫
    openImmersionIdealCokernelIso i u ≪≫
    closedImmersionPushforwardCokernelIso iU

/-- The chart pushforward isomorphism preserves the actual quotient maps. -/
theorem openImmersionClosedImmersionPushforwardIso_quotient
    {Y Z U : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (u : U ⟶ Y) [IsOpenImmersion u] :
    let iU := pullback.fst u i
    (Scheme.Modules.restrictFunctor u).map
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) ≫
        (openImmersionClosedImmersionPushforwardIso i u).hom =
      (Scheme.Modules.restrictUnitIso u).hom ≫
        IdealSheafDataModule.closedImmersionUnitToPushforwardUnit iU := by
  let iU := pullback.fst u i
  let R := Scheme.Modules.restrictFunctor u
  let c := IdealSheafDataModule.closedImmersionModuleToUnit i
  let cU := IdealSheafDataModule.closedImmersionModuleToUnit iU
  let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i
  let qU := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit iU
  let eR := openImmersionRestrictPushforwardCokernelIso i u
  let eC := openImmersionIdealCokernelIso i u
  let eU := closedImmersionPushforwardCokernelIso iU
  let t := Scheme.Modules.restrictUnitIso u
  have hR : cokernel.π (R.map c) ≫ eR.hom = R.map q :=
    openImmersionRestrictPushforwardCokernelIso_π i u
  have hC : cokernel.π (R.map c) ≫ eC.hom = t.hom ≫ cokernel.π cU :=
    openImmersionIdealCokernelIso_π i u
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


end PfaffianDescent
